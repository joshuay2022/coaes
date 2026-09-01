/-
Copyright (c) 2025 Alex Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Best, Jannis Limperg
-/

import CoAes

/-! Test case for clause indentation. We require CoAes tactic clauses to be on
the same line or indented, to prevent CoAes from mistaking the following
tactics for clauses. -/

example : ∃ n : Nat, n ^ 2 = 4 ∧ ∃ n : Nat, n ^ 2 = 9 ∧ True := by
  coaes
    (config := { maxRuleApplications := 1, warnOnNonterminal := false })
  (exists 2)
  (exists 3)

example : ∃ n : Nat, n ^ 2 = 4 ∧ ∃ n : Nat, n ^ 2 = 9 ∧ True := by
  coaes (config := { maxRuleApplications := 1, warnOnNonterminal := false })
  (exists 2)
  (exists 3)
