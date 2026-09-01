/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

structure MyTrue₁
structure MyTrue₂

@[coaes safe]
structure MyTrue₃ where
  tt : MyTrue₁

/--
warning: coaes: failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : MyTrue₃ := by
  coaes
  apply MyTrue₁.mk

@[coaes safe]
structure MyFalse where
  falso : False

/--
warning: coaes: failed to prove the goal after exhaustive search.
---
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : MyFalse := by
  coaes

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : MyFalse := by
  coaes (config := { terminal := true })

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : MyFalse := by
  coaes (config := { warnOnNonterminal := false })

@[coaes safe]
structure MyFalse₂ where
  falso : False
  tt : MyTrue₃

/--
warning: coaes: failed to prove the goal after exhaustive search.
---
error: unsolved goals
case falso
⊢ False

case tt
⊢ MyTrue₁
-/
#guard_msgs in
example : MyFalse₂ := by
  coaes

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
set_option coaes.warn.nonterminal false in
example : MyFalse := by
  coaes

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
set_option coaes.warn.nonterminal true in
example : MyFalse := by
  coaes (config := { warnOnNonterminal := false })
