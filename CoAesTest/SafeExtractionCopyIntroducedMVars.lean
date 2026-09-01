/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true

axiom P : Prop
axiom T : Prop
axiom Q : Nat → Prop
axiom R : Nat → Prop
axiom S : Nat → Prop

@[coaes safe]
axiom q_r_p : ∀ x, Q x → R x → P

@[coaes safe]
axiom s_q : ∀ x y, S y → Q x

@[coaes safe]
axiom s_r : ∀ x y, S y → R x

axiom s : S 0

/--
warning: coaes: failed to prove the goal after exhaustive search.
---
error: unsolved goals
case a.a
⊢ S ?a.y✝

case a.a
⊢ S ?a.y✝

case x
⊢ Nat

case a.a
⊢ S ?a.y✝

case a.a
⊢ S ?a.y✝

case x
⊢ Nat
---
error: (kernel) declaration has metavariables '_example'
-/
#guard_msgs in
example : P := by
  coaes
