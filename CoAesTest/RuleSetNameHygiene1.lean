/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAesTest.RuleSetNameHygiene0

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

macro "coaes_test" : tactic => `(tactic| coaes (rule_sets := [test]))

@[coaes safe (rule_sets := [test])]
structure TT where

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : TT := by
  coaes (config := { terminal := true })

example : TT := by
  coaes_test
