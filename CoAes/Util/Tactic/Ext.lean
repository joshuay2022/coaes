/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import CoAes.Tracing

public section

open Lean Lean.Meta Lean.Elab.Tactic.Ext

namespace CoAes

structure ExtResult where
  depth : Nat
  commonFVarIds : Array FVarId
  goals : Array (MVarId × Array FVarId)

partial def straightLineExt (goal : MVarId) : MetaM ExtResult :=
  go goal 0 #[]
where
  go (goal : MVarId) (depth : Nat) (commonFVarIds : Array FVarId) :
      MetaM ExtResult:= do
    withConstCoAesTraceNode .debug (return m!"straightLineExt") do
    coaes_trace[debug] "goal:{indentD goal}"
    let goals? ← show MetaM _ from observing? $ applyExtTheoremAt goal
    if let some goals := goals? then
      coaes_trace[debug] "ext lemma applied; new goals:{indentD $ Elab.goalsToMessageData goals}"
      let goals := goals.toArray
      if goals.isEmpty then
        return { depth := depth + 1, goals := #[], commonFVarIds := #[] }
      let goals ← goals.mapM λ goal => do
        let (fvarIds, goal) ← goal.intros
        return (goal, fvarIds)
      if h : goals.size = 1 then
        let (goal, fvarIds) := goals[0]
        go goal (depth + 1) (commonFVarIds ++ fvarIds)
      else
        return { depth := depth + 1, goals, commonFVarIds }
    else
      coaes_trace[debug] "no applicable ext lemma"
      return { depth, goals := #[(goal, #[])], commonFVarIds }

def straightLineExtProgress (goal : MVarId) : MetaM ExtResult := do
  let result ← straightLineExt goal
  if result.depth == 0 then
    throwError "no applicable extensionality theorem found"
  return result

end CoAes
