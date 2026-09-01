/-
Copyright (c) 2022-2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAesTest.RuleSets0

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

@[coaes safe (rule_sets := [test_A])]
inductive A : Prop where
| intro

@[coaes safe (rule_sets := [test_B])]
inductive B : Prop where
| intro

@[coaes safe]
inductive C : Prop where
| intro

inductive D : Prop where
| intro

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : A := by
  coaes (config := { terminal := true })

example : A := by
  coaes (rule_sets := [test_A])

example : B := by
  coaes (rule_sets := [test_A, test_B])

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : C := by
  coaes (rule_sets := [-default]) (config := { terminal := true })

example : C := by
  coaes

attribute [coaes safe (rule_sets := [test_C])] C

-- Removing the attribute removes all rules associated with C from all rule
-- sets.
attribute [-coaes] C

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : C := by
  coaes (rule_sets := [test_C]) (config := { terminal := true })

example : C := by
  coaes (add safe C)

@[coaes norm simp]
theorem ad : D ↔ A :=
  ⟨λ _ => A.intro, λ _ => D.intro⟩

example : D := by
  coaes (rule_sets := [test_A])

attribute [-coaes] ad

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : D := by
  coaes (rule_sets := [test_A]) (config := { terminal := true })

example : D := by
  coaes (add norm ad) (rule_sets := [test_A])

-- Rules can also be local.

inductive E : Prop where
  | intro

section

attribute [local coaes safe] E

example : E := by
  coaes

end

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : E := by
  coaes (config := { terminal := true })

example : E := by
  constructor

-- Rules can also be scoped.

namespace EScope

attribute [scoped coaes safe] E

example : E := by
  coaes

end EScope

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : E := by
  coaes (config := { terminal := true })

example : E := by
  open EScope in coaes
