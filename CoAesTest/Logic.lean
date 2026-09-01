/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true

example : True := by
  coaes

example : Unit := by
  coaes

example : PUnit.{u} := by
  coaes

example (h : False) : α := by
  coaes

example (h : Empty) : α := by
  coaes

example (h : PEmpty.{u}) : α := by
  coaes
