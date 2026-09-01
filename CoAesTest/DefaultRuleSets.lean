/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAesTest.DefaultRuleSetsInit

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

@[coaes norm unfold (rule_sets := [regular₁])]
def T := True

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : T := by
  coaes (config := { terminal := true })

example : T := by
  coaes (rule_sets := [regular₁])

@[coaes norm unfold (rule_sets := [regular₂, dflt₁])]
def U := True

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : U := by
  coaes (rule_sets := [-dflt₁]) (config := { terminal := true })

example : U := by
  coaes
