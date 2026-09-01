/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

def T := Empty

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : Empty := by
  coaes (erase CoAes.BuiltinRules.applyHyps)
    (config := { assumptionTransparency := .reducible, terminal := true })

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : T) : Empty := by
  coaes (erase CoAes.BuiltinRules.applyHyps)
    (config := { assumptionTransparency := .reducible, terminal := true })

example (h : T) : Empty := by
  coaes (erase CoAes.BuiltinRules.applyHyps)

@[irreducible] def U := False

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (h : U) : False := by
  coaes (config := { terminal := true })

example (h : U) : False := by
  coaes (config := { assumptionTransparency := .all })
