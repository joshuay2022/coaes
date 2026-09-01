/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true

structure A

open Lean.Elab.Tactic in
@[coaes norm]
def tac : TacticM Unit := do
  evalTactic $ ← `(tactic| exact A.mk)

example : A := by
  set_option coaes.check.script false in
  set_option coaes.check.script.steps false in
  coaes
