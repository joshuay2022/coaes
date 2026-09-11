/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import CoAes.Exception
public import CoAes.Search.Expansion

public section

open Lean Lean.Meta

namespace CoAes

declare_coaes_exception
  safeExpansionFailedException safeExpansionFailedExceptionId
  isSafeExpansionFailedException

structure SafeExpansionM.State where
  numRapps : Nat := 0

abbrev SafeExpansionM Q [Queue Q] := StateRefT SafeExpansionM.State (SearchM Q)

variable [Queue Q]

private def Goal.isSafeExpanded (g : Goal) : BaseIO Bool :=
  (pure g.unsafeRulesSelected) <||> g.hasSafeRapp

-- Typeclass inference struggles with inferring Q, so we have to lift
-- explicitly.
private def liftSearchM (x : SearchM Q α) : SafeExpansionM Q α :=
  x

mutual
  private partial def expandSafePrefixGoal (gref : GoalRef) :
      SafeExpansionM Q Unit := do
    let g ← gref.get
    if g.state.isProven then
      coaes_trace[steps] "Skipping safe rule expansion of goal {g.id} since it is already proven."
      return
    if ! (← g.isSafeExpanded) then
      coaes_trace[steps] "Applying safe rules to goal {g.id}."
      if ← liftSearchM $ normalizeGoalIfNecessary gref then
          -- Goal was already proved by normalisation.
          return
      let maxRapps := (← read).options.maxSafePrefixRuleApplications
      if maxRapps > 0 && (← getThe SafeExpansionM.State).numRapps > maxRapps then
        throw safeExpansionFailedException
      discard $ liftSearchM $ runFirstSafeRule gref
      modifyThe SafeExpansionM.State λ s =>
        { s with numRapps := s.numRapps + 1 }
    else
      coaes_trace[steps] "Skipping safe rule expansion of goal {g.id} since safe rules have already been applied."
    let g ← gref.get
    if g.state.isProven then
      return
    let safeRapps ← g.safeRapps
    if h₁ : 0 < safeRapps.size then
      if safeRapps.size > 1 then
        throwError "coaes: internal error: goal {g.id} has multiple safe rapps"
      expandFirstPrefixRapp safeRapps[0]

  private partial def expandFirstPrefixRapp (rref : RappRef) :
      SafeExpansionM Q Unit := do
    (← rref.get).children.forM expandSafePrefixMVarCluster

  private partial def expandSafePrefixMVarCluster (cref : MVarClusterRef) :
      SafeExpansionM Q Unit := do
    (← cref.get).goals.forM expandSafePrefixGoal
end

/-- Outcome of expanding the safe prefix of the search tree. -/
inductive SafePrefixExpansionResult
  /-- The safe prefix was fully expanded. -/
  | complete
  /-- Expansion stopped at the `maxSafePrefixRuleApplications` limit. -/
  | ruleLimit
  /-- Expansion stopped because a resource limit (e.g. `maxHeartbeats`) was
  reached. -/
  | resourceLimit
  deriving Inhabited, BEq

def SafePrefixExpansionResult.isComplete : SafePrefixExpansionResult → Bool
  | .complete => true
  | _ => false

def expandSafePrefix : SearchM Q SafePrefixExpansionResult := do
  coaes_trace[steps] "Expanding safe subtree of the root goal."
  -- `tryCatchRuntimeEx` so that a resource limit (e.g. `maxHeartbeats`) hit
  -- while expanding the safe prefix stops the expansion gracefully, like the
  -- rule application limit: whatever was expanded so far is kept and the
  -- caller reports that the prefix is incomplete. Without this, the wrap-up
  -- after an otherwise successful search would fail with a bare timeout and
  -- the partial results (in particular the `coaes?` script) would be lost.
  tryCatchRuntimeEx
    (do expandSafePrefixGoal (← getRootGoal) |>.run' {}
        return .complete)
    (λ e => do
      if isSafeExpansionFailedException e then
        return .ruleLimit
      else if isResourceLimitException e then
        coaes_trace[steps] "Safe prefix expansion hit a resource limit: {e.toMessageData}"
        return .resourceLimit
      else
        throw e)

end CoAes
