/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

-- CoAes note: the builtin closing rules (`simp`, `omega`, `grind`, ...) would
-- prove some of this file's goals outright, defeating the purpose of the
-- test. They are erased for this file.
erase_coaes_rules
  [CoAes.BuiltinRules.closeSimp, CoAes.BuiltinRules.closeSimpAll,
   CoAes.BuiltinRules.closeOmega, CoAes.BuiltinRules.closeDecide,
   CoAes.BuiltinRules.closeGrind]


open Lean Lean.Meta

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

def unfoldConst («from» to : Name) : Simp.Simproc := λ e =>
  if e.isConstOf «from» then
    return .done { expr := .const to [] }
  else
    return .continue

@[irreducible] def T₁ := True

/--
error: tactic 'coaes' failed, made no progress
-/
#guard_msgs in
example : T₁ := by
  coaes

simproc unfoldT₁ (T₁) := unfoldConst ``T₁ ``True

example : T₁ := by
  coaes

/--
error: tactic 'coaes' failed, made no progress
-/
#guard_msgs in
example : T₁ := by
  coaes (config := { useDefaultSimpSet := false })

@[irreducible] def T₂ := True

/--
error: tactic 'coaes' failed, made no progress
-/
#guard_msgs in
example : T₂ := by
  coaes

simproc [coaes_builtin] unfoldT₂ (T₂) := unfoldConst ``T₂ ``True

/--
error: tactic 'coaes' failed, made no progress
-/
#guard_msgs in
example : T₂ := by
  coaes (rule_sets := [-builtin])

example : T₂ := by
  coaes
