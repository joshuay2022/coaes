/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

example (h : False) : α := by
  coaes

def T := False

variable {α : Type}

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : α := by
  coaes (config := { terminal := true })

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : α := by
  coaes (add safe cases (transparency! := reducible) False)
    (config := { terminal := true })

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : α := by
  coaes (add safe cases (transparency := default) False)
    (config := { terminal := true })

example (h : T) : α := by
  coaes (add safe cases (transparency! := default) False)

def U := T

example (h : U) : α := by
  coaes (add safe cases (transparency! := default) False)
