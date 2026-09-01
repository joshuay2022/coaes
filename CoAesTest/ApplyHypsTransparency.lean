/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

def T := Unit → Nat

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : Nat := by
  coaes (config := { applyHypsTransparency := .reducible, terminal := true })

example (h : T) : Nat := by
  coaes

@[irreducible] def U := Empty

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : Unit → Empty) : U := by
  coaes (config := { applyHypsTransparency := .reducible, terminal := true })

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : Unit → Empty) : U := by
  coaes (config := { terminal := true })

example (h : Unit → Empty) : U := by
  coaes (config := { applyHypsTransparency := .all })
