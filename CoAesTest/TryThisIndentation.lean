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


/--
info: Try this:

  [apply]     intro a_1 a_2
    simp_all
-/
#guard_msgs in
example {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y::l := by
  coaes?

/--
info: Try this:

  [apply]   simp_all
-/
#guard_msgs in
example {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y::l := by
  intros
  have : ¬ a ∈ y :: l := by
    coaes?
  exact this
