/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

-- Composite terms are supported by the `apply` and `forward` builders...

structure A where

/--
error: tactic 'coaes' failed, made no progress
-/
#guard_msgs in
example (h : A → β → γ) (b : β) : γ := by
  coaes

example (h : A → β → γ) (b : β) : γ := by
  coaes (add safe apply (h {}))

example (h : A → β → γ) (b : β) : γ := by
  coaes (add safe forward (h {}))

-- ... and also by the `simp` builder.

/--
error: tactic 'coaes' failed, made no progress
-/
#guard_msgs in
example {P : α → Prop} (h : A → x = y) (p : P x) : P y := by
  coaes

example {P : α → Prop} (h : A → x = y) (p : P x) : P y := by
  coaes (add simp (h {}))

/--
error: tactic 'coaes' failed, made no progress
-/
#guard_msgs in
example {P : α → Prop} (h₁ : A → x = y) (h₂ : A → y = z) (p : P x) : P z := by
  coaes

example {P : α → Prop} (h₁ : A → x = y) (h₂ : A → y = z) (p : P x) : P z := by
  coaes (add simp [(h₁ {}), (h₂ {})])
