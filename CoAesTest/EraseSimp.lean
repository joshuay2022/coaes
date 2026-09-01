/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
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

example (n : Nat) : n + m = m + n := by
  coaes (add simp Nat.add_comm)

attribute [local simp] Nat.add_comm

example (n : Nat) : n + m = m + n := by
  coaes

/--
error: tactic 'coaes' failed, made no progress
-/
#guard_msgs in
example (n : Nat) : n + m = m + n := by
  coaes (erase Nat.add_comm) (config := { warnOnNonterminal := false })

/--
error: tactic 'coaes' failed, made no progress
-/
#guard_msgs in
example (n : Nat) : n + m = m + n := by
  coaes (erase norm simp Nat.add_comm) (config := { warnOnNonterminal := false })

/--
error: coaes: 'Nat.add_comm' is not registered (with the given features) in any rule set.
-/
#guard_msgs in
example (n : Nat) : n + m = m + n := by
  coaes (erase apply Nat.add_comm)
