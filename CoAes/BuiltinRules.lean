/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- The CoAes.BuiltinRules.* imports are needed to ensure that the tactics from
-- these files are registered.
module

public import CoAes.BuiltinRules.Assumption
public import CoAes.BuiltinRules.ApplyHyps
public import CoAes.BuiltinRules.Closers
public import CoAes.BuiltinRules.DestructProducts
public import CoAes.BuiltinRules.Ext
public import CoAes.BuiltinRules.Intros
public import CoAes.BuiltinRules.Rfl
public import CoAes.BuiltinRules.Split
public import CoAes.BuiltinRules.Subst
public import CoAes.Frontend.Attribute

public section

namespace CoAes.BuiltinRules

attribute [coaes (rule_sets := [builtin]) safe 0 apply] PUnit.unit

-- Hypotheses of product type are split by a separate builtin rule because the
-- `cases` builder currently cannot be used for norm rules.
attribute [coaes (rule_sets := [builtin]) safe 101 constructors]
  And Prod PProd MProd

attribute [coaes (rule_sets := [builtin]) unsafe 30% constructors]
  Exists Subtype Sigma PSigma

-- Sums are split and introduced lazily.
attribute [coaes (rule_sets := [builtin]) [safe 100 cases, 50% constructors]]
  Or Sum PSum

-- A goal ⊢ P ↔ Q is split into ⊢ P → Q and ⊢ Q → P. Hypotheses of type `P ↔ Q`
-- are treated as equations `P = Q` by the simplifier and by our builtin subst
-- rule.
attribute [coaes (rule_sets := [builtin]) safe 100 constructors] Iff

-- A negated goal Γ ⊢ ¬ P is transformed into Γ, P ⊢ ⊥. A goal with a
-- negated hypothesis Γ, h : ¬ P ⊢ Q is transformed into Γ[P := ⊥] ⊢ Q[P := ⊥]
-- by the simplifier. Quantified negated hypotheses h : ∀ x : T, ¬ P x are also
-- supported by the simplifier if the premises x can be discharged.
@[coaes (rule_sets := [builtin]) safe 0]
theorem not_intro (h : P → False) : ¬ P := h

@[coaes (rule_sets := [builtin]) norm destruct]
theorem empty_false (h : Empty) : False := nomatch h

@[coaes (rule_sets := [builtin]) norm destruct]
theorem pEmpty_false (h : PEmpty) : False := nomatch h

attribute [coaes (rule_sets := [builtin]) norm constructors] ULift

attribute [coaes (rule_sets := [builtin]) norm 0 destruct] ULift.down

@[coaes (rule_sets := [builtin]) norm simp]
theorem heq_iff_eq (x y : α) : x ≍ y ↔ x = y :=
  ⟨eq_of_heq, heq_of_eq⟩

end CoAes.BuiltinRules
