/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import CoAes.RuleTac.Basic

public section

open Lean
open Lean.Meta

namespace CoAes

/--
Runs `x` with a fresh heartbeat budget for a single rule application, as
configured by the `maxRuleHeartbeats` option. This limits the damage a single
expensive rule can do: it fails with a heartbeat exception once its own budget
is exhausted, instead of consuming the whole `maxHeartbeats` budget of the
`coaes` call.
-/
def withRuleHeartbeatLimit [Monad m] [MonadLiftT CoreM m]
    [MonadControlT CoreM m] (opts : Options') (x : m α) : m α := do
  let outerMax := (← show CoreM _ from read).maxHeartbeats
  if outerMax == 0 && opts.maxRuleHeartbeats == 0 then
    -- `maxHeartbeats 0`: everything is unlimited.
    x
  else
    let budget :=
      if opts.maxRuleHeartbeats != 0 then
        opts.maxRuleHeartbeats * 1000
      else
        max 1 (outerMax / 10)
    withCurrHeartbeats do
      mapCoreM (withTheReader Core.Context
        (λ ctx => { ctx with maxHeartbeats := budget })) x

/--
Returns `true` if `e` was caused by a resource limit (`maxHeartbeats` or
`maxRecDepth`). Unlike `Exception.isRuntime`, this also detects a heartbeat
exception that a tactic (e.g. `simp`) caught and re-threw wrapped in a regular
error ("Tactic `simp` failed with a nested error: (deterministic) timeout
..."): the wrapped message still contains the `runtime.maxHeartbeats` tag.
-/
def isResourceLimitException (e : Exception) : Bool :=
  e.isRuntime ||
  match e with
  | .error _ msg =>
    msg.hasTag (λ n => n == `runtime.maxHeartbeats || n == `runtime.maxRecDepth)
  | _ => false

/--
Runs `x` with a fresh heartbeat budget of `percent` percent of `base` (which
should be the ambient `maxHeartbeats` budget captured when `coaes` was
entered; `0` means unlimited).

CoAes divides the ambient budget into slices — the search itself, the safe
prefix expansion, the proof extraction and the script generation each get one
— rather than letting the search consume everything. This serves two purposes:
the wrap-up still has budget after a search that ran out of time (so the
partial results, in particular the `coaes?` script, are reported), and the
slices add up to less than the ambient budget, so the elaboration that follows
the `coaes` call is not starved.
-/
def withHeartbeatBudget [Monad m] [MonadLiftT CoreM m] [MonadControlT CoreM m]
    (base percent : Nat) (x : m α) : m α := do
  if base == 0 then
    x
  else
    withCurrHeartbeats do
      mapCoreM (withTheReader Core.Context
        (λ ctx => { ctx with maxHeartbeats := max 1 (base * percent / 100) })) x

/--
Records that a rule failed because it exceeded a resource limit (heartbeats or
recursion depth). These rules are reported in a warning after the search.
-/
def recordResourceLimitedRule [Monad m] [MonadStats m]
    (name : DisplayRuleName) : m Unit :=
  modifyStats λ s =>
    if s.resourceLimitedRules.contains name then
      s
    else
      { s with resourceLimitedRules := s.resourceLimitedRules.push name }

def runRuleTac (tac : RuleTac) (ruleName : RuleName)
    (preState : Meta.SavedState) (input : RuleTacInput) :
    BaseM (Except Exception RuleTacOutput) := do
  let result ←
    -- `tryCatchRuntimeEx` also catches runtime exceptions (in particular the
    -- `maxHeartbeats` exception), which a regular `try ... catch` deliberately
    -- rethrows. A rule that runs out of its heartbeat budget is thus treated
    -- like any other failed rule and the search goes on. User interrupts are
    -- never caught.
    tryCatchRuntimeEx
      (Except.ok <$> runInMetaState preState do
        withRuleHeartbeatLimit input.options do
          tac input)
      (λ e => do
        if isResourceLimitException e then
          recordResourceLimitedRule (.ruleName ruleName)
          restoreState preState
        return .error e)
  if ← Check.rules.isEnabled then
    if let .ok ruleOutput := result then
      ruleOutput.applications.forM λ rapp => do
        if let (some err) ← rapp.check input then
          throwError "{Check.rules.name}: while applying rule {ruleName}: {err}"
  return result

end CoAes
