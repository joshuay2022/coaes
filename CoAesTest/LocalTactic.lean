/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
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

/--
error: tactic 'coaes' failed, made no progress
-/
#guard_msgs in
example (m n : Nat) : m * n = n * m := by
  coaes

example (m n : Nat) : m * n = n * m := by
  coaes (add safe (by rw [Nat.mul_comm]))

example (m n : Nat) : m * n = n * m := by
  coaes (add safe tactic (by rw [Nat.mul_comm m n]))

/--
error: tactic 'coaes' failed, made no progress
-/
#guard_msgs in
example (m n : Nat) : m * n = n * m := by
  coaes (add safe (by rw [Nat.mul_comm m m]))

example (m n : Nat) : m * n = n * m := by
  coaes (add safe (by apply Nat.mul_comm; done))
