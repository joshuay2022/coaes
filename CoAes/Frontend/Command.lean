/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public meta import CoAes.Frontend.Basic
public meta import CoAes.Stats.Report
public meta import Batteries.Linter.UnreachableTactic
public meta import CoAes.Frontend.Extension
public meta import CoAes.Frontend.RuleExpr

public meta section

open Lean Lean.Elab Lean.Elab.Command

namespace CoAes.Frontend.Parser

syntax (name := declareRuleSets)
  "declare_coaes_rule_sets " "[" ident,+,? "]"
  (" (" &"default" " := " CoAes.bool_lit ")")? : command

elab_rules : command
  | `(declare_coaes_rule_sets [ $ids:ident,* ]
       $[(default := $dflt?:CoAes.bool_lit)]?) => do
    let rsNames := (ids : Array Ident).map (·.getId)
    let dflt := (← dflt?.mapM (elabBoolLit ·)).getD false
    rsNames.forM checkRuleSetNotDeclared
    elabCommand $ ← `(meta initialize ($(quote rsNames).forM $ declareRuleSetUnchecked (isDefault := $(quote dflt))))
    -- TODO: record dependency on rule set at use site
    recordExtraRevUseOfCurrentModule

elab (name := addRules)
    attrKind:attrKind "add_coaes_rules " e:CoAes.rule_expr : command => do
  let attrKind :=
    match attrKind with
    | `(Lean.Parser.Term.attrKind| local) => .local
    | `(Lean.Parser.Term.attrKind| scoped) => .scoped
    | _ => .global
  let rules ← liftTermElabM do
    let e ← RuleExpr.elab e |>.run (← ElabM.Context.forAdditionalGlobalRules)
    e.buildAdditionalGlobalRules none
  for (rule, rsNames) in rules do
    for rsName in rsNames do
      addGlobalRule rsName rule attrKind (checkNotExists := true)

initialize Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``addRules

elab (name := eraseRules)
    "erase_coaes_rules " "[" es:CoAes.rule_expr,* "]" : command => do
  let filters ← Elab.Command.liftTermElabM do
    let ctx ← ElabM.Context.forGlobalErasing
    (es : Array _).mapM λ e => do
      let e ← RuleExpr.elab e |>.run ctx
      e.toGlobalRuleFilters
  for fs in filters do
    for (rsFilter, rFilter) in fs do
      eraseGlobalRules rsFilter rFilter (checkExists := true)

syntax (name := showRules)
  withPosition("#coaes_rules" (colGt ppSpace ident)*) : command

elab_rules : command
  | `(#coaes_rules $ns:ident*) => do
    liftTermElabM do
      let lt := λ (n₁, _) (n₂, _) => n₁.cmp n₂ |>.isLT
      let rss ←
        if ns.isEmpty then
          let rss ← getDeclaredGlobalRuleSets
          pure $ rss.qsort lt
        else
          ns.mapM λ n => return (n.getId, ← getGlobalRuleSet n.getId)
      TraceOption.ruleSet.withEnabled do
        for (name, rs, _) in rss do
          withConstCoAesTraceNode .ruleSet (return m!"Rule set '{name}'") do
            rs.trace .ruleSet

def evalStatsReport? (name : Name) : CoreM (Option StatsReport) := do
  try
    unsafe evalConstCheck StatsReport ``StatsReport name
  catch _ =>
    return none

syntax (name := showStats) withPosition("#coaes_stats " (colGt ident)?) : command

elab_rules : command
  | `(#coaes_stats) => do
    logInfo $ StatsReport.default $ ← getStatsArray
  | `(#coaes_stats $report:ident) => do
    let openDecl := OpenDecl.simple ``CoAes.StatsReport []
    withScope (λ s => { s with openDecls := openDecl :: s.openDecls }) do
      let names ← resolveGlobalConst report
      liftTermElabM do
        for name in names do
          if let some report ← evalStatsReport? name then
            logInfo $ report $ ← getStatsArray
            break
        throwError "'{report}' is not a constant of type 'CoAes.StatsReport'"

end CoAes.Frontend.Parser
