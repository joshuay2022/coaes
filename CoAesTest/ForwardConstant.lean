/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

structure Foo where
  foo ::

/--
error: tactic 'coaes' failed, made no progress
-/
#guard_msgs in
example : Foo := by
  coaes

example : Foo := by
  coaes (add safe forward Foo.foo)
