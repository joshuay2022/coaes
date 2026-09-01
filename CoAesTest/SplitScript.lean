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

open Classical

inductive MyFalse : Prop

/--
info: Try this:

  [apply]     split
    next h => sorry
    next h => sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {A B : Prop} : if P then A else B := by
  coaes? (config := { warnOnNonterminal := false })
  all_goals sorry

/--
info: Try this:

  [apply]     split at h
    next h_1 => simp_all
    next h_1 => simp_all
-/
#guard_msgs in
example (h : if P then A else B) : A ∨ B := by
  coaes?

/--
info: Try this:

  [apply]     split at h
    next n => simp_all
    next n => simp_all
    next n_1 x x_1 => simp_all
-/
#guard_msgs in
theorem foo (n : Nat) (h : match n with | 0 => A | 1 => B | _ => C) :
    A ∨ B ∨ C := by
  set_option coaes.check.rules false in -- TODO simp introduces mvar
  set_option coaes.check.tree false in
  coaes?
