/-
CoAes closing rules: standalone tactics (`simp`, `simp_all`, `omega`, `decide`,
`grind`) that are tried eagerly, before any other norm rule — in particular
before `intros` (penalty -100). Only `unfold` has higher priority.

Each rule succeeds only if the tactic closes the goal, and its script step
records the bare tactic syntax, so `coaes?` reports the simple tactic (`simp`)
rather than a decorated variant (`simp only [...]`).
-/
module

public import CoAes.Frontend.Attribute

public section

open Lean Lean.Meta
open Lean.Elab.Tactic (evalTactic withoutRecover)

namespace CoAes.RuleTac

/--
Builds a `RuleTac` that runs the tactic `stx` and succeeds only if it closes
the goal. The script step records `stx` verbatim.
-/
meta def closingTacticSyntax (stx : Syntax.Tactic) : RuleTac :=
  RuleTac.ofSingleRuleTac λ input => do
    unless input.options.enableClosers do
      throwError "closing rules are disabled (options := \{ ..., enableClosers := false })"
    -- Closing a goal that shares metavariables with other goals would assign
    -- those metavariables during normalisation, which normalisation rules must
    -- not do (cf. the analogous check in `normSimpCore`).
    unless input.mvars.isEmpty do
      throwError "closing rules do not run on goals with metavariables"
    let preState ← saveState
    let postGoals ←
      Lean.Elab.Tactic.run input.goal (withoutRecover $ evalTactic stx) |>.run'
    unless postGoals.isEmpty do
      throwError "tactic '{stx}' did not close the goal"
    let postState ← saveState
    let step : Script.LazyStep := {
      preGoal := input.goal
      tacticBuilders := #[return .unstructured stx]
      postGoals := #[]
      preState, postState
    }
    return (#[], some #[step], none)

end CoAes.RuleTac

namespace CoAes.BuiltinRules

@[coaes (rule_sets := [builtin]) norm -150 tactic]
meta def closeSimp : RuleTac :=
  RuleTac.closingTacticSyntax $ Unhygienic.run `(tactic| simp)

@[coaes (rule_sets := [builtin]) norm -149 tactic]
meta def closeSimpAll : RuleTac :=
  RuleTac.closingTacticSyntax $ Unhygienic.run `(tactic| simp_all)

@[coaes (rule_sets := [builtin]) norm -148 tactic]
meta def closeOmega : RuleTac :=
  RuleTac.closingTacticSyntax $ Unhygienic.run `(tactic| omega)

@[coaes (rule_sets := [builtin]) norm -147 tactic]
meta def closeDecide : RuleTac :=
  RuleTac.closingTacticSyntax $ Unhygienic.run `(tactic| decide)

@[coaes (rule_sets := [builtin]) norm -146 tactic]
meta def closeGrind : RuleTac :=
  RuleTac.closingTacticSyntax $ Unhygienic.run `(tactic| grind)

end CoAes.BuiltinRules
