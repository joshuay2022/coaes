/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import CoAes.Check
public import CoAes.Options
public import CoAes.RuleSet
public import CoAes.Script.Check
public import CoAes.Script.Main
public import CoAes.Search.Expansion
public import CoAes.Search.ExpandSafePrefix
public import CoAes.Search.Queue
public import CoAes.Tree
public import CoAes.Frontend.Extension

public section

open Lean
open Lean.Elab.Tactic (liftMetaTacticAux TacticM)
open Lean.Parser.Tactic (tacticSeq)
open Lean.Meta

namespace CoAes

variable [CoAes.Queue Q]

/-! ### Heartbeat budget distribution

CoAes splits the ambient `maxHeartbeats` budget into slices rather than letting
the search consume all of it. The wrap-up after the search (safe prefix
expansion, proof extraction, script generation) then still has budget even
when the search ran out of time, so its partial results are reported instead
of lost; and since the slices add up to less than 100%, the elaboration that
follows the `coaes` call is not starved either. -/

/-- Percentage of the ambient heartbeat budget given to the proof search. -/
def searchHeartbeatPercent := 60

/-- Percentage of the ambient heartbeat budget given to safe prefix expansion. -/
def safePrefixHeartbeatPercent := 10

/-- Percentage of the ambient heartbeat budget given to proof extraction. -/
def extractHeartbeatPercent := 10

/-- Percentage of the ambient heartbeat budget given to script generation. -/
def scriptHeartbeatPercent := 15

partial def nextActiveGoal : SearchM Q GoalRef := do
  let some gref ← popGoal?
    | throwError "coaes/expandNextGoal: internal error: no active goals left"
  if ! (← (← gref.get).isActive) then
    nextActiveGoal
  else
    return gref

def expandNextGoal : SearchM Q Unit := do
  let gref ← nextActiveGoal
  let g ← gref.get
  let (initialGoal, initialMetaState) ←
    g.currentGoalAndMetaState (← getRootMetaState)
  let result ← withCoAesTraceNode .steps
    (fmt g.id g.priority initialGoal initialMetaState) do
    initialMetaState.runMetaM' do
      coaes_trace[steps] "Initial goal:{indentD initialGoal}"
    let maxRappDepth := (← read).options.maxRuleApplicationDepth
    if maxRappDepth != 0 && (← gref.get).depth >= maxRappDepth then
      coaes_trace[steps] "Treating the goal as unprovable since it is beyond the maximum rule application depth ({maxRappDepth})."
      gref.markForcedUnprovable
      setMaxRuleApplicationDepthReached
      return .failed
    let result ← expandGoal gref
    let currentIteration ← getIteration
    gref.modify λ g => g.setLastExpandedInIteration currentIteration
    if ← (← gref.get).isActive then
      enqueueGoals #[gref]
    return result
  match result with
  | .proved newRapps | .succeeded newRapps => traceNewRapps newRapps
  | .failed => return
  where
    fmt (id : GoalId) (priority : Percent) (initialGoal : MVarId)
        (initialMetaState : Meta.SavedState)
        (result : Except Exception RuleResult) : SearchM Q MessageData := do
      let tgt ← initialMetaState.runMetaM' do
        initialGoal.withContext do
          addMessageContext $ toMessageData (← initialGoal.getType)
      return m!"{exceptRuleResultToEmoji (·.toEmoji) result} (G{id}) [{priority.toHumanString}] ⋯ ⊢ {tgt}"

    traceNewRapps (newRapps : Array RappRef) : SearchM Q Unit := do
      coaes_trace[steps] do
        for rref in newRapps do
          let r ← rref.get
          r.withHeadlineTraceNode .steps
            (transform := λ msg => return m!"{newNodeEmoji} " ++ msg) do
            withCoAesTraceNode .steps (λ _ => return "Metadata") do
              r.traceMetadata .steps
          r.metaState.runMetaM' do
            r.forSubgoalsM λ gref => do
              let g ← gref.get
              g.withHeadlineTraceNode .steps
                (transform := λ msg => return m!"{newNodeEmoji} " ++ msg) do
                coaes_trace![steps] g.preNormGoal
                withCoAesTraceNode .steps (λ _ => return "Metadata") do
                  g.traceMetadata .steps

def checkGoalLimit : SearchM Q (Option MessageData) := do
  let maxGoals := (← read).options.maxGoals
  let currentGoals := (← getTree).numGoals
  if maxGoals != 0 && currentGoals >= maxGoals then
    return m!"maximum number of goals ({maxGoals}) reached. Set the 'maxGoals' option to increase the limit."
  return none

def checkRappLimit : SearchM Q (Option MessageData) := do
  let maxRapps := (← read).options.maxRuleApplications
  let currentRapps := (← getTree).numRapps
  if maxRapps != 0 && currentRapps >= maxRapps then
    return m!"maximum number of rule applications ({maxRapps}) reached. Set the 'maxRuleApplications' option to increase the limit."
  return none

def checkRootUnprovable : SearchM Q (Option MessageData) := do
  let root := (← getTree).root
  if (← root.get).state.isUnprovable then
    let msg ←
      if ← wasMaxRuleApplicationDepthReached then
        pure m!"failed to prove the goal. Some goals were not explored because the maximum rule application depth ({(← read).options.maxRuleApplicationDepth}) was reached. Set option 'maxRuleApplicationDepth' to increase the limit."
      else
        pure m!"failed to prove the goal after exhaustive search."
    return msg
  return none

def getProof? : SearchM Q (Option Expr) := do
  getExprMVarAssignment? (← getRootMVarId)

def finalizeProof : SearchM Q Unit := do
  (← getRootMVarId).withContext do
    extractProof
    let (some proof) ← getProof? | throwError
      "coaes: internal error: root goal is proven but its metavariable is not assigned"
    if (← instantiateMVars proof).hasExprMVar then
      let inner :=
        m!"Proof: {proof}\nUnassigned metavariables: {(← getMVarsNoDelayed proof).map (·.name)}"
      throwError "coaes: internal error: extracted proof has metavariables.{indentD inner}"
    withPPAnalyze do
      coaes_trace[proof] "Final proof:{indentExpr proof}"

def traceScript (completeProof : Bool) : SearchM Q Unit :=
  profiling (λ stats _ elapsed => { stats with script := elapsed }) do
  let options := (← read).options
  if ! options.generateScript then
    return
  -- Script generation runs with a fresh heartbeat budget: the search may well
  -- have exhausted the ambient one, and reporting the script the search
  -- already found is exactly what is wanted in that case. If generation
  -- itself exceeds the budget, report that instead of failing the tactic.
  tryCatchRuntimeEx
    (withHeartbeatBudget (← read).baseMaxHeartbeats scriptHeartbeatPercent do
      let (uscript, proofHasMVars) ←
        if completeProof then extractScript else extractSafePrefixScript
      uscript.checkIfEnabled
      let rootGoal ← getRootMVarId
      let rootState ← getRootMetaState
      coaes_trace[script] "Unstructured script:{indentD $ toMessageData $ ← uscript.renderTacticSeq rootState rootGoal}"
      let sscript? ← uscript.optimize proofHasMVars rootState rootGoal
      checkAndTraceScript uscript sscript? rootState rootGoal options
        (expectCompleteProof := completeProof) "coaes")
    (λ e => do
      unless isResourceLimitException e do
        throw e
      logWarning m!"coaes: could not generate a tactic script because a resource limit (e.g. 'maxHeartbeats') was reached.")

def traceTree : SearchM Q Unit := do
  (← (← getRootGoal).get).traceTree .tree

def finishIfProven : SearchM Q Bool := do
  unless (← (← getRootMVarCluster).get).state.isProven do
    return false
  finalizeProof
  traceScript (completeProof := true)
  traceTree
  return true

-- TODO move to Tree directory
/--
This function detects whether the search has made progress, meaning that the
remaining goals after safe prefix expansion are different from the initial goal.
We approximate this by checking whether, after safe prefix expansion, either
of the following statements is true.

- There is a safe rapp.
- A subgoal of the preprocessing rule has been modified during normalisation.

This is an approximation because a safe rule could, in principle, leave the
initial goal unchanged.
-/
def treeHasProgress : TreeM Bool := do
  let resultRef ← IO.mkRef false
  preTraverseDown
    (λ gref => do
      let g ← gref.get
      if let some postGoal := g.normalizationState.normalizedGoal? then
        if postGoal != g.preNormGoal then
          resultRef.set true
          return false
      return true)
    (λ rref => do
      let rule := (← rref.get).appliedRule
      if rule.name == preprocessRule.name then
        return true
      else if rule.isUnsafe then
        return false
      else
        resultRef.set true
        return false)
    (λ _ => return true)
    (.mvarCluster (← getThe Tree).root)
  resultRef.get

def throwCoAesEx (mvarId : MVarId) (remainingSafeGoals : Array MVarId)
    (safePrefixExpansion : SafePrefixExpansionResult)
    (msg? : Option MessageData) : SearchM Q α := do
  if coaes.smallErrorMessages.get (← getOptions) then
    match msg? with
    | none => throwError "tactic 'coaes' failed"
    | some msg => throwError "tactic 'coaes' failed, {msg}"
  else
    let maxRapps := (← read).options.maxSafePrefixRuleApplications
    let suffix :=
      if remainingSafeGoals.isEmpty then
        m!""
      else
        let gs := .joinSep (remainingSafeGoals.toList.map toMessageData) "\n\n"
        let suffix' :=
          match safePrefixExpansion with
          | .complete => m!""
          | .ruleLimit =>
            m!"\nThe safe prefix was not fully expanded because the maximum number of rule applications ({maxRapps}) was reached."
          | .resourceLimit =>
            m!"\nThe safe prefix was not fully expanded because a resource limit (e.g. 'maxHeartbeats') was reached."
        m!"\nRemaining goals after safe rules:{indentD gs}{suffix'}"
    -- Copy-pasta from `Lean.Meta.throwTacticEx`
    match msg? with
    | none => throwError "tactic 'coaes' failed\nInitial goal:{indentD mvarId}{suffix}"
    | some msg => throwError "tactic 'coaes' failed, {msg}\nInitial goal:{indentD mvarId}{suffix}"


-- When we hit a non-fatal error (i.e. the search terminates without a proof
-- because the root goal is unprovable or because we hit a search limit), we
-- usually:
--
-- - Expand all safe rules as much as possible, starting from the root node,
--   until we hit an unsafe rule. We call this the safe prefix.
-- - Extract the proof term for the safe prefix and report the remaining goals.
--
-- The first step is necessary because a goal can become unprovable due to a
-- sibling being unprovable, without the goal ever being expanded. So if we did
-- not expand the safe rules after the fact, the tactic's output would be
-- sensitive to minor changes in, e.g., rule priority.
/--
Marks every goal that is still un-normalised as normalised-without-changes.

Proof and script extraction require that every goal in the tree has been
normalised. Normally the search guarantees this, but when safe prefix
expansion is interrupted (by the rule application limit or by a resource
limit) it can leave freshly created goals un-normalised. Such a goal is simply
used as it is; it ends up as one of the remaining goals of the `coaes` call.
-/
def normaliseRemainingGoals : SearchM Q Unit := do
  let root := (← getTree).root
  preTraverseDown
    (λ gref => do
      let g ← gref.get
      if g.normalizationState matches .notNormal then
        let (_, postState) ← g.runMetaMInParentState (pure ())
        gref.modify (·.setNormalizationState (.normal g.preNormGoal postState #[]))
      return true)
    (λ _ => return true)
    (λ _ => return true)
    (.mvarCluster root)

def handleNonfatalError (err : MessageData) : SearchM Q (Array MVarId) := do
  -- The search may have exhausted its heartbeat budget (that is one of the
  -- reasons we end up here), so each wrap-up phase gets its own fresh slice of
  -- the ambient budget. Otherwise reporting the results of a search that ran
  -- out of time would itself run out of time and the partial results — in
  -- particular the `coaes?` script — would be lost.
  let base := (← read).baseMaxHeartbeats
  let safeExpansionSuccess ←
    withHeartbeatBudget base safePrefixHeartbeatPercent expandSafePrefix
  unless safeExpansionSuccess.isComplete do
    normaliseRemainingGoals
  let safeGoals ←
    -- Extracting the proof term for the safe prefix can also exceed a resource
    -- limit. Report what we have (no safe goals) rather than failing.
    tryCatchRuntimeEx
      (withHeartbeatBudget base extractHeartbeatPercent extractSafePrefix)
      λ e => do
        unless isResourceLimitException e do
          throw e
        logWarning m!"coaes: could not extract the goals remaining after the safe rules because a resource limit (e.g. 'maxHeartbeats') was reached."
        return #[]
  coaes_trace[proof] do
    match ← getProof? with
    | some proof =>
      (← getRootMVarId).withContext do
        coaes_trace![proof] "{proof}"
    | none => coaes_trace![proof] "<no proof>"
  traceTree
  traceScript (completeProof := false)
  let opts := (← read).options
  if opts.terminal then
    throwCoAesEx (← getRootMVarId) safeGoals safeExpansionSuccess err
  if ! (← treeHasProgress) then
    throwCoAesEx (← getRootMVarId) #[] safeExpansionSuccess "made no progress"
  if opts.warnOnNonterminal && coaes.warn.nonterminal.get (← getOptions) then
    logWarning m!"coaes: {err}"
  match safeExpansionSuccess with
  | .complete => pure ()
  | .ruleLimit =>
    logWarning m!"coaes: safe prefix was not fully expanded because the maximum number of rule applications ({(← read).options.maxSafePrefixRuleApplications}) was reached."
  | .resourceLimit =>
    logWarning m!"coaes: safe prefix was not fully expanded because a resource limit (e.g. 'maxHeartbeats') was reached."
  safeGoals.mapM (clearForwardImplDetailHyps ·)

partial def searchLoop : SearchM Q (Array MVarId) :=
  withIncRecDepth do
    checkSystem "coaes"
    if let (some err) ← checkRootUnprovable then
      handleNonfatalError err
    else if ← finishIfProven then
      return #[]
    else if let (some err) ← checkGoalLimit then
      handleNonfatalError err
    else if let (some err) ← checkRappLimit then
      handleNonfatalError err
    else
      expandNextGoal
      checkInvariantsIfEnabled
      incrementIteration
      searchLoop

def search (goal : MVarId) (ruleSet? : Option LocalRuleSet := none)
     (options : CoAes.Options := {}) (simpConfig : Simp.Config := {})
     (simpConfigSyntax? : Option Term := none) (stats : Stats := {}) :
     MetaM (Array MVarId × Stats) := do
  goal.checkNotAssigned `coaes
  let options ← options.toOptions'
  let ruleSet ←
    match ruleSet? with
    | none =>
        let rss ← Frontend.getDefaultGlobalRuleSets
        mkLocalRuleSet rss options
    | some ruleSet => pure ruleSet
  let ⟨Q, _⟩ := options.queue
  let go : SearchM _ _ := do
    show SearchM Q _ from
    try
      -- If the overall `maxHeartbeats` budget (or the recursion depth limit)
      -- is exhausted during the search, report the progress made so far —
      -- like any other search limit — instead of failing with the resource
      -- error. User interrupts are never caught. The wrap-up (safe prefix
      -- expansion, script generation) runs with a fresh heartbeat budget.
      tryCatchRuntimeEx
        (withHeartbeatBudget (← read).baseMaxHeartbeats searchHeartbeatPercent
          searchLoop) λ e => do
        unless isResourceLimitException e do
          throw e
        let msg :=
          if e.isMaxHeartbeat then
            m!"failed to prove the goal: the search was stopped because the overall heartbeat budget was exhausted. Set option 'maxHeartbeats' to increase the limit."
          else
            m!"failed to prove the goal: the search was stopped because a resource limit was reached: {e.toMessageData}"
        -- `handleNonfatalError` runs with a fresh heartbeat budget.
        handleNonfatalError msg
    finally freeTree
  let ((goals, _, _), stats) ←
    go.run ruleSet options simpConfig simpConfigSyntax? goal |>.run stats
  return (goals, stats)

end CoAes
