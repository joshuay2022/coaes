/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import CoAes

set_option coaes.check.all true

attribute [coaes unsafe 50% constructors] List.Mem

@[coaes safe [constructors, cases (cases_patterns := [All _ [], All _ (_ :: _)])]]
inductive All (P : α → Prop) : List α → Prop where
  | none : All P []
  | more (x xs) : P x → All P xs → All P (x :: xs)

theorem weaken (P Q : α → Prop) (wk : ∀ x, P x → Q x) (xs : List α) (h : All P xs)
  : All Q xs := by
  induction h <;> coaes

theorem in_self (xs : List α) : All (· ∈ xs) xs := by
  induction xs
  case nil =>
    coaes
  case cons x xs ih =>
    have wk : ∀ a, a ∈ xs → a ∈ x :: xs := by coaes
    have ih' : All (fun a => a ∈ x :: xs) xs := by coaes (add unsafe 1% weaken)
    coaes
