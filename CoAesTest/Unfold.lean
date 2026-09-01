/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- Inspired by this Zulip discussion:
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Goal.20state.20not.20updating.2C.20bugs.2C.20etc.2E/near/338356062

import CoAes

set_option coaes.check.all true

structure WalkingPair

def WidePullbackShape A B := Sum A B

abbrev WalkingCospan : Type := WidePullbackShape Empty Empty

@[coaes norm destruct]
def WalkingCospan_elim : WalkingCospan → Sum Empty Empty := id

/--
info: Try this:

  [apply]     unfold WalkingCospan at h
    unfold WidePullbackShape at h
    cases h with
    | inl val => grind
    | inr val_1 => grind
-/
#guard_msgs in
example (h : WalkingCospan) : α := by
  coaes? (add norm unfold [WidePullbackShape, WalkingCospan])

example (h : WalkingCospan) : α := by
  coaes (add norm simp [WidePullbackShape, WalkingCospan])

@[coaes norm unfold]
def Foo := True

@[coaes norm unfold]
def Bar := False

/--
info: Try this:

  [apply]     unfold Bar Foo
    unfold Foo at h₁
    unfold Foo Bar at h₂
    simp_all
    cases h₂ with
    | inl val =>
      simp_all
      apply PSum.inr
      simp
    | inr val_1 => simp_all
-/
#guard_msgs in
example (h₁ : Foo) (h₂ : PSum Foo Bar) : PSum Bar Foo := by
  coaes?
