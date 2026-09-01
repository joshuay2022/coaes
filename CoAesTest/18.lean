/-
Copyright (c) 2022 Asta H. From. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asta H. From, Jannis Limperg
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

attribute [coaes safe cases (cases_patterns := [List.Mem _ []])] List.Mem
attribute [coaes unsafe 50% cases (cases_patterns := [List.Mem _ (_ :: _)])] List.Mem

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
theorem Mem.split [DecidableEq α] (xs : List α) (v : α) (h : v ∈ xs)
  : ∃ l r, xs = l ++ v :: r := by
  induction xs
  case nil =>
    coaes
  case cons x xs ih =>
    have dec : Decidable (x = v) := inferInstance
    cases dec
    case isFalse no =>
      coaes (config := { terminal := true }) (erase CoAes.BuiltinRules.ext)
    case isTrue yes =>
      apply Exists.intro []
      apply Exists.intro xs
      rw [yes]
      rfl
