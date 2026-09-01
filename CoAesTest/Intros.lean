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

def Injective₁ (f : α → β) := ∀ x y, f x = f y → x = y

abbrev Injective₂ (f : α → β) := ∀ x y, f x = f y → x = y

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : Injective₁ (@id Nat) := by
  coaes (config := { terminal := true })

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : Injective₁ (@id Nat) := by
  coaes (config := { introsTransparency? := some .reducible, terminal := true })

example : Injective₁ (@id Nat) := by
  coaes (config := { introsTransparency? := some .default })

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : Injective₂ (@id Nat) := by
  coaes (config := { terminal := true })

example : Injective₂ (@id Nat) := by
  coaes (config := { introsTransparency? := some .reducible })

example : Injective₂ (@id Nat) := by
  coaes (config := { introsTransparency? := some .default })
