/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import CoAes.Frontend.Attribute

public section

open Lean Lean.Elab.Tactic

namespace CoAes.BuiltinRules

@[coaes safe 0 (rule_sets := [builtin])]
meta def rfl : RuleTac :=
  RuleTac.ofTacticSyntax λ _ => `(tactic| rfl)

end CoAes.BuiltinRules
