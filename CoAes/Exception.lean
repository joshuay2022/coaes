/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Lean

public section

open Lean

namespace CoAes

scoped macro "declare_coaes_exception"
    excName:ident idName:ident testName:ident : command =>
  `(initialize $idName : InternalExceptionId ←
      Lean.registerInternalExceptionId $(quote $ `CoAes ++ excName.getId)

    def $excName : Exception :=
      .internal $idName

    def $testName : Exception → Bool
      | .internal id _ => id == $idName
      | _ => false)

end CoAes
