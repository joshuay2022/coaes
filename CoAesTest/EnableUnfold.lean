/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

@[coaes norm unfold]
def T := True

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : T := by
  coaes (config := { enableUnfold := false, terminal := true })

example : T := by
  coaes
