/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

@[coaes 50% constructors]
inductive I₁
  | ofI₁ : I₁ → I₁
  | ofTrue : True → I₁

example : I₁ := by
  coaes

example : I₁ := by
  coaes (config := { strategy := .bestFirst })

example : I₁ := by
  coaes (config := { strategy := .breadthFirst })

/--
error: tactic 'coaes' failed, maximum number of rule applications (10) reached. Set the 'maxRuleApplications' option to increase the limit.
-/
#guard_msgs in
example : I₁ := by
  coaes (config :=
    { strategy := .depthFirst
      maxRuleApplicationDepth := 0
      maxRuleApplications := 10,
      terminal := true })

example : I₁ := by
  coaes (config := { strategy := .depthFirst, maxRuleApplicationDepth := 10 })
