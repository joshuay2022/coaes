/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true

def Involutive (f : α → α) : Prop :=
  ∀ x, f (f x) = x

example : Involutive not := by
  coaes (add norm simp Involutive)

example : Involutive not := by
  coaes (add norm unfold Involutive)
