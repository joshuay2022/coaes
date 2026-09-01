/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

-- Forward rules always operate at reducible transparency.

def T := Unit → Empty

variable {α : Type}

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) (u : Unit) : α := by
  coaes (config := { terminal := true })

def U := Unit

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) (u : U) : α := by
  coaes (config := { terminal := true })

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) (u : U) : α := by
  coaes (add forward safe h) (config := { terminal := true })

abbrev V := Unit

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : Unit → Empty) (u : V) : α := by
  coaes (config := { terminal := true })

example (h : Unit → Empty) (u : V) : α := by
  coaes (add forward safe h)
