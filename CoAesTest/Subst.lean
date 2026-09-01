/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

-- CoAes note: the builtin closing rules (`simp`, `omega`, `grind`, ...) would
-- prove some of this file's goals outright, defeating the purpose of the
-- test. They are erased for this file.
erase_coaes_rules
  [CoAes.BuiltinRules.closeSimp, CoAes.BuiltinRules.closeSimpAll,
   CoAes.BuiltinRules.closeOmega, CoAes.BuiltinRules.closeDecide,
   CoAes.BuiltinRules.closeGrind]


set_option coaes.check.all true
set_option coaes.smallErrorMessages true

-- These test cases test the builtin subst tactic.

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h₁ : x = 5) (h₂ : y = 5) : x = y := by
  coaes (erase CoAes.BuiltinRules.subst)
    (config := { useSimpAll := false, terminal := true })

example (h₁ : x = 5) (h₂ : y = 5) : x = y := by
  coaes (config := { useSimpAll := false })

variable {α : Type}

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example {x y z : α} (h₁ : x = y) (h₂ : y = z) : x = z := by
  coaes (erase CoAes.BuiltinRules.subst)
    (config := { useSimpAll := false, terminal := true })

example {x y z : α} (h₁ : x = y) (h₂ : y = z) : x = z := by
  coaes (config := { useSimpAll := false })

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example {x y : α }(P : ∀ x y, x = y → Prop) (h₁ : x = y) (h₂ : P x y h₁) :
    x = y := by
  coaes
    (erase CoAes.BuiltinRules.subst, CoAes.BuiltinRules.assumption,
           CoAes.BuiltinRules.applyHyps)
    (config := { useSimpAll := false, terminal := true })

example {x y : α }(P : ∀ x y, x = y → Prop) (h₁ : x = y) (h₂ : P x y h₁) :
    x = y := by
  coaes
    (erase CoAes.BuiltinRules.assumption,
           CoAes.BuiltinRules.applyHyps)
    (config := { useSimpAll := false })

-- Subst also works for bi-implications.

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h₁ : P ↔ Q) (h₂ : Q ↔ R) (h₃ : P) : R  := by
  coaes (erase CoAes.BuiltinRules.subst)
    (config := { useSimpAll := false, terminal := true })

example (h₁ : P ↔ Q) (h₂ : Q ↔ R) (h₃ : P) : R  := by
  coaes (config := { useSimpAll := false })

-- Subst also works for morally-homogeneous heterogeneous equalities (using a
-- builtin simp rule which turns these into actual homogeneous equalities).

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example {P : α → Prop} {x y z : α} (h₁ : x ≍ y) (h₂ : y ≍ z) (h₃ : P x) :
    P z  := by
  coaes (erase CoAes.BuiltinRules.subst)
    (config := { useSimpAll := false, terminal := true })

example {P : α → Prop} {x y z : α} (h₁ : x ≍ y) (h₂ : y ≍ z) (h₃ : P x) :
    P z  := by
  coaes (config := { useSimpAll := false })
