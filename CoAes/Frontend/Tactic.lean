/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import CoAes.Frontend.RuleExpr
public import CoAes.Options
public import Batteries.Linter.UnreachableTactic
public import CoAes.Frontend.Extension

public section

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Term

namespace CoAes.Frontend.Parser

declare_syntax_cat CoAes.tactic_clause

syntax ruleSetSpec := "-"? ident

syntax " (" &"add " CoAes.rule_expr,+,? ")" : CoAes.tactic_clause
syntax " (" &"erase " CoAes.rule_expr,+,? ")" : CoAes.tactic_clause
syntax " (" &"rule_sets" " := " "[" ruleSetSpec,+,? "]" ")" : CoAes.tactic_clause
syntax " (" &"config" " := " term ")" : CoAes.tactic_clause
syntax " (" &"simp_config" " := " term ")" : CoAes.tactic_clause
syntax " (" &"defs" " := " "[" ident,*,? "]" ")" : CoAes.tactic_clause
syntax " (" &"no_unfold" " := " "[" ident,*,? "]" ")" : CoAes.tactic_clause

/--
`coaes <clause>*` tries to solve the current goal by applying a set of rules
registered with the `@[coaes]` attribute. See [its
README](https://github.com/JLimperg/coaes#readme) for a tutorial and a
reference.

The variant `coaes?` prints the proof it found as a `Try this` suggestion.

Clauses can be used to customise the behaviour of an CoAes call. Available
clauses are:

- `(add <phase> <priority> <builder> <rule>)` adds a rule. `<phase>` is
  `unsafe`, `safe` or `norm`. `<priority>` is a percentage for unsafe rules and
  an integer for safe and norm rules. `<rule>` is the name of a declaration or
  local hypothesis. `<builder>` is the rule builder used to turn `<rule>` into
  an CoAes rule. Example: `(add unsafe 50% apply Or.inl)`.
- `(erase <rule>)` disables a globally registered CoAes rule. Example: `(erase
  CoAes.BuiltinRules.assumption)`.
- `(rule_sets := [<ruleset>,*])` enables or disables named sets of rules for
  this CoAes call. Example: `(rule_sets := [-builtin, MyRuleSet])`.
- `(config { <opt> := <value> })` adjusts CoAes's search options. See
  `CoAes.Options`.
- `(simp_config { <opt> := <value> })` adjusts options for CoAes's built-in
  `simp` rule. The given options are directly passed to `simp`. For example,
  `(simp_config := { zeta := false })` makes CoAes use
  `simp (config := { zeta := false })`.
- `(defs := [<decl>,*])` registers the given definitions as unfold rules.
  Unfolding has the highest priority of all rules. Unlike
  `(add norm unfold <decl>)`, recursive definitions are allowed: each
  definition is unfolded at most once per goal, so unfolding cannot loop.
  Example: `(defs := [Function.comp, myDef])`.
- `(no_unfold := [<decl>,*])` prevents the given definitions from being
  unfolded, even if they are registered as unfold rules (via `defs`, `add` or
  the `@[coaes]` attribute). Use this to avoid unfolding definitions that
  should stay folded. Example: `(no_unfold := [myRecursiveDef])`.
-/
syntax (name := coaesTactic)  "coaes" (ppSpace colGt CoAes.tactic_clause)* : tactic

@[inherit_doc coaesTactic]
syntax (name := coaesTactic?) "coaes?" (ppSpace colGt CoAes.tactic_clause)* : tactic

meta initialize do
  Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``coaesTactic
  Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``coaesTactic?

end Parser

-- Inspired by declare_config_elab
unsafe def elabConfigUnsafe (type : Name) (stx : Syntax) : TermElabM α :=
  withRef stx do
    let e ← withoutModifyingStateWithInfoAndMessages <| withLCtx {} {} <| withSaveInfoContext <| Term.withSynthesize <| withoutErrToSorry do
      let e ← Term.elabTermEnsuringType stx (Lean.mkConst type)
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    evalExpr' α type e

def elabOptions : Syntax → TermElabM CoAes.Options :=
  unsafe elabConfigUnsafe ``CoAes.Options

def elabSimpConfig : Syntax → TermElabM Simp.Config :=
  unsafe elabConfigUnsafe ``Simp.Config

def elabSimpConfigCtx : Syntax → TermElabM Simp.ConfigCtx :=
  unsafe elabConfigUnsafe ``Simp.ConfigCtx

structure TacticConfig where
  additionalRules : Array RuleExpr
  erasedRules : Array RuleExpr
  enabledRuleSets : Std.HashSet RuleSetName
  options : CoAes.Options
  simpConfig : Simp.Config
  simpConfigSyntax? : Option Term
  /-- Definitions to unfold, from `(defs := [...])`. Unfolding has the highest
  priority of all rules. Recursive definitions are allowed; each definition is
  unfolded at most once per goal. -/
  unfoldDefs : Array Name := #[]
  /-- Definitions that must not be unfolded, from `(no_unfold := [...])`. -/
  noUnfold : Array Name := #[]

namespace TacticConfig

def parse (stx : Syntax) (goal : MVarId) : TermElabM TacticConfig :=
  withRef stx do
    match stx with
    | `(tactic| coaes $clauses:CoAes.tactic_clause*) =>
      go (traceScript := false) clauses
    | `(tactic| coaes? $clauses:CoAes.tactic_clause*) =>
      go (traceScript := true) clauses
    | _ => throwUnsupportedSyntax
  where
    go (traceScript : Bool) (clauses : Array (TSyntax `CoAes.tactic_clause)) :
        TermElabM TacticConfig := do
      let init : TacticConfig := {
        additionalRules := #[]
        erasedRules := #[]
        enabledRuleSets := ← getDefaultRuleSetNames
        options := { traceScript }
        simpConfig := {}
        simpConfigSyntax? := none
      }
      let (_, config) ← clauses.forM (addClause traceScript) |>.run init
      let simpConfig ←
        if let some stx := config.simpConfigSyntax? then
          if config.options.useSimpAll then
            (·.toConfig) <$> elabSimpConfigCtx stx
          else
            elabSimpConfig stx
        else
          if config.options.useSimpAll then
            pure { : Simp.ConfigCtx}.toConfig
          else
            pure { : Simp.Config }
        return { config with simpConfig }

    addClause (traceScript : Bool) (stx : TSyntax `CoAes.tactic_clause) :
        StateRefT TacticConfig TermElabM Unit :=
      withRef stx do
        match stx with
        | `(tactic_clause| (add $es:CoAes.rule_expr,*)) => do
          let rs ← (es : Array Syntax).mapM λ e =>
            RuleExpr.elab e |>.run $ .forAdditionalRules goal
          modify λ c => { c with additionalRules := c.additionalRules ++ rs }
        | `(tactic_clause| (erase $es:CoAes.rule_expr,*)) => do
          let rs ← (es : Array Syntax).mapM λ e =>
            RuleExpr.elab e |>.run $ .forErasing goal
          modify λ c => { c with erasedRules := c.erasedRules ++ rs }
        | `(tactic_clause| (rule_sets := [ $specs:ruleSetSpec,* ])) => do
          let mut enabledRuleSets := (← get).enabledRuleSets
          for spec in (specs : Array Syntax) do
            match spec with
            | `(Parser.ruleSetSpec| - $rsName:ident) => do
              let rsName := RuleSetName.elab rsName
              unless enabledRuleSets.contains rsName do throwError
                "coaes: trying to deactivate rule set '{rsName}', but it is not active"
              enabledRuleSets := enabledRuleSets.erase rsName
            | `(Parser.ruleSetSpec| $rsName:ident) => do
              let rsName := RuleSetName.elab rsName
              if enabledRuleSets.contains rsName then throwError
                "coaes: rule set '{rsName}' is already active"
              enabledRuleSets := enabledRuleSets.insert rsName
            | _ => throwUnsupportedSyntax
          modify λ c => { c with enabledRuleSets }
        | `(tactic_clause| (config := $t:term)) =>
          let options ← elabOptions t
          let options :=
            { options with traceScript := options.traceScript || traceScript }
          modify λ c => { c with options }
        | `(tactic_clause| (simp_config := $t:term)) =>
          modify λ c => { c with simpConfigSyntax? := some t }
        | `(tactic_clause| (defs := [ $ids:ident,* ])) => do
          let decls ← (ids : Array Syntax).mapM λ id =>
            resolveUnfoldableDef id
          modify λ c => { c with unfoldDefs := c.unfoldDefs ++ decls }
        | `(tactic_clause| (no_unfold := [ $ids:ident,* ])) => do
          let decls ← (ids : Array Syntax).mapM λ id =>
            resolveGlobalConstNoOverload id
          modify λ c => { c with noUnfold := c.noUnfold ++ decls }
        | _ => throwUnsupportedSyntax

    resolveUnfoldableDef (id : Syntax) :
        StateRefT TacticConfig TermElabM Name := do
      let decl ← resolveGlobalConstNoOverload id
      let info ← getConstInfo decl
      unless info matches .defnInfo .. do throwError
        "coaes: (defs := [...]): '{decl}' is not a definition"
      return decl

def updateRuleSet (rs : LocalRuleSet) (c : TacticConfig) (goal : MVarId):
    TermElabM LocalRuleSet := do
  let mut rs := rs
  for ruleExpr in c.additionalRules do
    let rules ← ruleExpr.buildAdditionalLocalRules goal
    for rule in rules do
      rs := rs.add rule

  -- Erase erased rules
  for ruleExpr in c.erasedRules do
    let filters ← ruleExpr.toLocalRuleFilters |>.run $ .forErasing goal
    for rFilter in filters do
      let (rs', anyErased) := rs.erase rFilter
      rs := rs'
      if ! anyErased then
        throwError "coaes: '{rFilter.name}' is not registered (with the given features) in any rule set."
  return rs

def getRuleSet (goal : MVarId) (c : TacticConfig) :
    TermElabM LocalRuleSet :=
  goal.withContext do
    let rss ← getGlobalRuleSets c.enabledRuleSets.toArray
    let mut rs ← c.updateRuleSet (← mkLocalRuleSet rss (← c.options.toOptions')) goal
    -- Add the unfold rules from `(defs := [...])`. Unlike the `unfold`
    -- builder, we do not reject recursive definitions: the normalisation
    -- state ensures that each definition is unfolded at most once per goal.
    for decl in c.unfoldDefs do
      let unfoldThm? ← getUnfoldEqnFor? decl
      rs := rs.add $ .global $ .base $ .unfoldRule { decl, unfoldThm? }
    -- Block the definitions from `(no_unfold := [...])`, including ones
    -- registered globally or via `(defs := [...])`.
    unless c.noUnfold.isEmpty do
      rs := { rs with
        unfoldRules := c.noUnfold.foldl (·.erase ·) rs.unfoldRules }
    return rs

end CoAes.Frontend.TacticConfig
