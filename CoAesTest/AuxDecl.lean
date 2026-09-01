/-
Copyright (c) 2025 Jannis Limperg. All rights reserved.
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


/-
This test case checks whether tactics that make use of auxiliary declarations,
such as `omega` and `bv_decide`, work with CoAes. Auxiliary declarations are
problematic because we can't allows tactics on different branches of the search
tree to add auxiliary declarations with the same name.
-/

theorem foo (m n : Nat) : n + m = m + n ∧ m + n = n + m := by
  fail_if_success coaes (config := { terminal := true })
  coaes (add safe (by omega))

local instance [Add α] [Add β] : Add (α × β) :=
  ⟨λ (a, b) (a', b') => (a + a', b + b')⟩

theorem bar
    (fst snd fst_1 snd_1 fst_2 snd_2 w w_1 w_2 w_3 : BitVec 128)
    (left : w_1.uaddOverflow w_3 = true)
    (left_1 : w.uaddOverflow w_2 = true)
    (right : (w_1 + w_3).uaddOverflow 1#128 = true) :
    (fst_2, snd_2) = (fst, snd) + (fst_1, snd_1) := by
  coaes (add safe (by bv_decide))

theorem baz (a b : BitVec 1) : (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) := by
  coaes (add safe 1000 (by bv_decide))
