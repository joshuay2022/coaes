/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Jannis Limperg
-/

-- Thanks to Jireh Loreaux for reporting this MWE.

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

@[irreducible]
def foo : Nat := 37

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : foo = 37 := by
  coaes (config := { terminal := true }) (erase CoAes.BuiltinRules.rfl)

example : foo = 37 := by
  unfold foo
  rfl

attribute [coaes norm unfold] foo

example : foo = 37 := by coaes (erase CoAes.BuiltinRules.rfl)

attribute [-coaes] foo

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : foo = 37 := by
  coaes (config := { terminal := true }) (erase CoAes.BuiltinRules.rfl)

example : foo = 37 := by
  unfold foo
  rfl
