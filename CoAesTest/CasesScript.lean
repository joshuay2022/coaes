/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true

@[coaes 50% cases]
inductive FancyAnd (α β : Prop) : Prop
  | dummy (p : Empty)
  | and (a : α) (b : β)

/--
info: Try this:

  [apply]     apply And.intro
    ·
      cases h with
      | dummy p => grind
      | and a b => simp_all
    ·
      cases h with
      | dummy p => grind
      | and a b => simp_all
-/
#guard_msgs in
example {α β} (h : FancyAnd α β) : α ∧ β := by
  coaes?

@[coaes safe cases (cases_patterns := [All _ [], All _ (_ :: _)])]
inductive All (P : α → Prop) : List α → Prop
  | nil : All P []
  | cons : P x → All P xs → All P (x :: xs)

@[coaes 99% constructors]
structure MyTrue : Prop

/--
info: Try this:

  [apply]     rcases h with ⟨⟩ | @⟨x_1, xs_1, a, a_1⟩
    apply MyTrue.mk
-/
#guard_msgs in
example {P : α → Prop} (h : All P (x :: xs)) : MyTrue := by
  coaes?
