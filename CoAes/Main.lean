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

end CoAes
