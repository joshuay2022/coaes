/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public meta import CoAes.Frontend.Extension
public meta import CoAes.Frontend.RuleExpr
public import CoAes.Frontend.Extension
public import CoAes.Frontend.RuleExpr

public meta section

open Lean
open Lean.Elab

namespace CoAes.Frontend

namespace Parser

declare_syntax_cat CoAes.attr_rules

syntax CoAes.rule_expr : CoAes.attr_rules
syntax "[" CoAes.rule_expr,+,? "]" : CoAes.attr_rules

syntax (name := coaes) "coaes " CoAes.attr_rules : attr

end Parser

structure AttrConfig where
  rules : Array RuleExpr
  deriving Inhabited

namespace AttrConfig

def «elab» (stx : Syntax) : TermElabM AttrConfig :=
  withRef stx do
    match stx with
    | `(attr| coaes $e:CoAes.rule_expr) => do
      let r ← RuleExpr.elab e |>.run $ ← ElabM.Context.forAdditionalGlobalRules
      return { rules := #[r] }
    | `(attr| coaes [ $es:CoAes.rule_expr,* ]) => do
      let ctx ← ElabM.Context.forAdditionalGlobalRules
      let rs ← (es : Array Syntax).mapM λ e => RuleExpr.elab e |>.run ctx
      return { rules := rs }
    | _ => throwUnsupportedSyntax

end AttrConfig


initialize registerBuiltinAttribute {
  name := `coaes
  descr := "Register a declaration as an CoAes rule."
  applicationTime := .afterCompilation
  add := λ decl stx attrKind => withRef stx do
    -- TODO: should be checked in any case where `decl` will be passed to `evalConst`
    --ensureAttrDeclIsMeta `coaes decl attrKind
    let rules ← runTermElabMAsCoreM do
      let config ← AttrConfig.elab stx
      config.rules.flatMapM (·.buildAdditionalGlobalRules decl)
    for (rule, rsNames) in rules do
      for rsName in rsNames do
        addGlobalRule rsName rule attrKind (checkNotExists := true)
  erase := λ decl =>
    let ruleFilter :=
      { name := decl, scope := .global, builders := #[], phases := #[] }
    eraseGlobalRules RuleSetNameFilter.all ruleFilter (checkExists := true)
}

end CoAes.Frontend
