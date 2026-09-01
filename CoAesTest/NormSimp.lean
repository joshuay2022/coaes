/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

-- A basic test for local simp rules.
example {α : Prop} (h : α) : α := by
  coaes (rule_sets := [-builtin,-default]) (add h norm simp)

-- This test checks that we don't 'self-simplify' hypotheses: `h` should not
-- be used to simplify itself.
example (h : (α ∧ β) ∨ γ) : α ∨ γ := by
  coaes (add h norm simp)

-- Ditto, but we can omit the 'norm'.
example (h : (α ∧ β) ∨ γ) : α ∨ γ := by
  coaes (add h simp)

-- This test checks that the norm simp config is passed around properly.

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example {α β : Prop} (ha : α) (h : α → β) : β := by
  coaes (rule_sets := [-builtin,-default])
    (simp_config := { maxDischargeDepth := 0 })
    (config := { terminal := true, useDefaultSimpSet := false })

example {α β : Prop} (ha : α) (h : α → β) : β := by
  coaes (rule_sets := [-builtin,-default])

-- Ditto.

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : true && false = false := by
  coaes (rule_sets := [-default,-builtin])
    (simp_config := { decide := false })
    (config := { terminal := true, useDefaultSimpSet := false })

example : true && false = false := by
  coaes (rule_sets := [-default,-builtin]) (simp_config := { decide := true })

-- We can use the `useSimpAll` config option to switch between `simp_all` and
-- `simp at *`.

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example {α : Prop} (ha : α) : α := by
  coaes (rule_sets := [-builtin,-default])
    (config := { useSimpAll := false, terminal := true })

example {α : Prop} (ha : α) : α := by
  coaes (rule_sets := [-builtin,-default])

-- We can give priorities to `simp` rules, corresponding to the priorities of
-- `simp` lemmas.

opaque T : Prop

@[coaes simp 1]
axiom TF : T ↔ False

@[coaes simp 2]
axiom TT : T ↔ True

example : T := by coaes

attribute [-coaes] TF
attribute [coaes simp 3] TF

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : T := by
  coaes (config := { terminal := true })

example : T := by
  rw [TT]; trivial
