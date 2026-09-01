/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import CoAes.Stats.Basic
public import Lean.Data.Position

open Lean

namespace CoAes

public structure StatsFileRecord extends Stats where
  file : String
  position : Option Position
  deriving ToJson

namespace StatsFileRecord

variable [Monad m] [MonadLog m] in
public protected def ofStats (coaesStx : Syntax) (stats : Stats) :
    m StatsFileRecord := do
  let file ← getFileName
  let fileMap ← getFileMap
  let position := coaesStx.getPos?.map fileMap.toPosition
  return { stats with file, position }

end StatsFileRecord

variable [Monad m] [MonadLog m] [MonadOptions m] [MonadLiftT IO m] in
public def appendStatsToStatsFileIfEnabled (coaesStx : Syntax) (stats : Stats) :
    m Unit := do
  let file := coaes.stats.file.get (← getOptions)
  if file == "" then
    return
  let record ← StatsFileRecord.ofStats coaesStx stats
  IO.FS.withFile file .append fun hdl => do
    -- Append mode atomically moves the cursor to EOF on write, so there is no
    -- race condition between locking the file and moving to EOF.
    hdl.lock (exclusive := true)
    try
      hdl.putStrLn <| toJson record |>.compress
    finally
      hdl.unlock

end CoAes
