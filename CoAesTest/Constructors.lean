/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

@[coaes safe]
inductive Even : Nat → Type
  | zero : Even 0
  | plusTwo : Even n → Even (n + 2)

example : Even 6 := by
  coaes

attribute [-coaes] Even

def T n := Even n

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : T 6 := by
  coaes (config := { terminal := true })

example : T 6 := by
  coaes (add safe constructors (transparency! := default) Even)
