/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

-- Basic examples

structure TT₁ where

/-- error: tactic 'coaes' failed, made no progress -/
#guard_msgs in
example : TT₁ := by
  coaes

add_coaes_rules safe TT₁

example : TT₁ := by
  coaes

-- Local rules

structure TT₂ where

namespace Test

local add_coaes_rules safe TT₂

example : TT₂ := by
  coaes

end Test

/-- error: tactic 'coaes' failed, made no progress -/
#guard_msgs in
example : TT₂ := by
  coaes

-- Scoped rules

structure TT₃ where

namespace Test

scoped add_coaes_rules safe TT₃

example : TT₃ := by
  coaes

end Test

/-- error: tactic 'coaes' failed, made no progress -/
#guard_msgs in
example : TT₃ := by
  coaes

def Test.example : TT₃ := by
  coaes

-- Tactics

structure TT₄ where

/-- error: tactic 'coaes' failed, made no progress -/
#guard_msgs in
example : TT₄ := by
  coaes

add_coaes_rules safe (by exact TT₄.mk)

example : TT₄ := by
  coaes

-- Multiple rules

axiom T : Type
axiom U : Type
axiom f : T → U
axiom t : T

/-- error: tactic 'coaes' failed, made no progress -/
#guard_msgs in
example : U := by
  coaes

add_coaes_rules safe [(by apply f), t]

noncomputable example : U := by
  coaes
