/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public meta import CoAes.Search.Main
public meta import CoAes.Frontend.Tactic
public meta import CoAes.Stats.Extension
public meta import CoAes.Stats.File

public section

open Lean
open Lean.Elab.Tactic

namespace CoAes

@[tactic Frontend.Parser.coaesTactic, tactic Frontend.Parser.coaesTactic?]
meta def evalCoAes : Tactic := λ stx => do
  profileitM Exception "coaes" (← getOptions) do
  let goal ← getMainGoal
  goal.withContext do
    let (_, stats) ← go stx goal |>.run ∅
    stats.trace .stats
    recordStatsForCurrentFileIfEnabled stx stats
    appendStatsToStatsFileIfEnabled stx stats
where
  go (stx : Syntax) (goal : MVarId) : StateRefT Stats TacticM Unit :=
    profiling (λ s _ t => { s with total := t }) do
      let config ← profiling (λ s _ t => { s with configParsing := t }) do
        Frontend.TacticConfig.parse stx goal
      let ruleSet ←
        profiling (λ s _ t => { s with ruleSetConstruction := t }) do
          config.getRuleSet goal
      withConstCoAesTraceNode .ruleSet (return "Rule set") do
        ruleSet.trace .ruleSet
      profiling (λ s _ t => { s with search := t }) do
        let (goals, stats) ←
          search goal ruleSet config.options config.simpConfig
            config.simpConfigSyntax? (← getStats)
        replaceMainGoal goals.toList
        modifyStats λ _ => stats
        warnAboutResourceLimitedRules config stats goals

  /--
  Rules that hit a resource limit (e.g. `maxHeartbeats`) during the search
  were treated as failed and the search continued without them. Report them,
  so that a user of `coaes?` knows that the returned tactics were found
  without these rules and can raise the limit if needed. The warning is shown
  when a script was requested (`coaes?`) or when the search did not close the
  goal.
  -/
  warnAboutResourceLimitedRules (config : Frontend.TacticConfig)
      (stats : Stats) (goals : Array MVarId) : TacticM Unit := do
    let rules := stats.resourceLimitedRules
    if rules.isEmpty then
      return
    unless config.options.traceScript || ! goals.isEmpty do
      return
    let fmtRule : DisplayRuleName → MessageData
      | .ruleName n => m!"{n.name}"
      | .normSimp => m!"<norm simp>"
      | .normUnfold => m!"<norm unfold>"
    let rulesList :=
      MessageData.joinSep (rules.toList.map fmtRule) ", "
    logWarning m!"coaes: the following rules were treated as failed because they exceeded a resource limit (e.g. 'maxHeartbeats'): {rulesList}\nThe search continued without them, so the result may be incomplete. Set option 'maxRuleHeartbeats' to give each rule more time."

end CoAes
