/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

set_option trace.coaes.proof true

/--
error: tactic 'coaes' failed, made no progress
---
trace: [coaes.proof] <no proof>
-/
#guard_msgs in
example : α := by
  coaes

@[coaes norm simp]
def F := False

set_option pp.mvars false in
/--
warning: coaes: failed to prove the goal after exhaustive search.
---
error: unsolved goals
⊢ False
---
trace: [coaes.proof] id ?_
-/
#guard_msgs in
example : F := by
  coaes
