/-
Copyright (c) 2022-2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import CoAes.Nanos
public import CoAes.Rule.Name
public import CoAes.Tracing
public import CoAes.Options.Public

public section

open Lean

namespace CoAes

-- All times are in nanoseconds.
structure RuleStats where
  rule : DisplayRuleName
  elapsed : Nanos
  successful : Bool
  deriving Inhabited, ToJson

namespace RuleStats

instance : ToString RuleStats where
  toString rp :=
    let success := if rp.successful then "successful" else "failed"
    s!"[{rp.elapsed.printAsMillis}] apply rule {rp.rule} ({success})"

end RuleStats

inductive ScriptGenerated.Method where
  | static
  | dynamic
  deriving Inhabited, ToJson

instance : ToString ScriptGenerated.Method where
  toString
    | .static => "static"
    | .dynamic => "dynamic"

structure ScriptGenerated where
  method : ScriptGenerated.Method
  perfect : Bool
  hasMVar : Bool
  deriving Inhabited, ToJson

namespace ScriptGenerated

protected def toString (g : ScriptGenerated) : String :=
  s!"with {if g.perfect then "perfect" else "imperfect"} {g.method} structuring"

end ScriptGenerated

structure Stats where
  total : Nanos
  configParsing : Nanos
  ruleSetConstruction : Nanos
  search : Nanos
  ruleSelection : Nanos
  script : Nanos
  scriptGenerated : Option ScriptGenerated
  ruleStats : Array RuleStats
  /--
  Rules that failed during the search because they exceeded a resource limit
  (heartbeats or recursion depth). Such rules are treated as ordinary failures
  — the search continues with other rules — and are reported in a warning.
  -/
  resourceLimitedRules : Array DisplayRuleName
  deriving Inhabited

namespace Stats

protected def empty : Stats where
  total := 0
  configParsing := 0
  ruleSetConstruction := 0
  search := 0
  ruleSelection := 0
  script := 0
  scriptGenerated := none
  ruleStats := #[]
  resourceLimitedRules := #[]

instance : EmptyCollection Stats :=
  ⟨Stats.empty⟩

end Stats


structure RuleStatsTotals where
  /--
  Number of successful applications of a rule.
  -/
  numSuccessful : Nat
  /--
  Number of failed applications of a rule.
  -/
  numFailed : Nat
  /--
  Total elapsed time of successful applications of a rule.
  -/
  elapsedSuccessful : Nanos
  /--
  Total elapsed time of failed applications of a rule.
  -/
  elapsedFailed : Nanos

namespace RuleStatsTotals

protected def empty : RuleStatsTotals where
  numSuccessful := 0
  numFailed := 0
  elapsedSuccessful := 0
  elapsedFailed := 0

instance : EmptyCollection RuleStatsTotals :=
  ⟨.empty⟩

def compareByTotalElapsed : (x y : RuleStatsTotals) → Ordering :=
  compareOn λ totals => totals.elapsedSuccessful + totals.elapsedFailed

end RuleStatsTotals


namespace Stats

def ruleStatsTotals (p : Stats)
    (init : Std.HashMap DisplayRuleName RuleStatsTotals := ∅) :
    Std.HashMap DisplayRuleName RuleStatsTotals :=
  p.ruleStats.foldl (init := init) λ m rp => Id.run do
    let mut stats := m.getD rp.rule ∅
    if rp.successful then
      stats := { stats with
        numSuccessful := stats.numSuccessful + 1
        elapsedSuccessful := stats.elapsedSuccessful + rp.elapsed
      }
    else
      stats := { stats with
        numFailed := stats.numFailed + 1
        elapsedFailed := stats.elapsedFailed + rp.elapsed
      }
    m.insert rp.rule stats

def _root_.CoAes.sortRuleStatsTotals
    (ts : Array (DisplayRuleName × RuleStatsTotals)) :
    Array (DisplayRuleName × RuleStatsTotals) :=
  let lt := λ (n₁, t₁) (n₂, t₂) =>
    RuleStatsTotals.compareByTotalElapsed t₁ t₂ |>.swap.then
    (compare n₁ n₂)
    |>.isLT
  ts.qsort lt

def trace (p : Stats) (opt : TraceOption) : CoreM Unit := do
  if ! (← opt.isEnabled) then
    return
  let totalRuleApplications :=
    p.ruleStats.foldl (init := 0) λ total rp =>
      total + rp.elapsed
  coaes_trace![opt] "Total: {p.total.printAsMillis}"
  coaes_trace![opt] "Configuration parsing: {p.configParsing.printAsMillis}"
  coaes_trace![opt] "Rule set construction: {p.ruleSetConstruction.printAsMillis}"
  coaes_trace![opt] "Script generation: {p.script.printAsMillis}"
  coaes_trace![opt] "Script generated: {match p.scriptGenerated with | none => "no" | some g => g.toString}"
  withConstCoAesTraceNode opt (collapsed := false)
      (return m!"Search: {p.search.printAsMillis}") do
    coaes_trace![opt] "Rule selection: {p.ruleSelection.printAsMillis}"
    withConstCoAesTraceNode opt (collapsed := false)
        (return m!"Rule applications: {totalRuleApplications.printAsMillis}") do
      let timings := sortRuleStatsTotals p.ruleStatsTotals.toArray
      for (n, t) in timings do
        coaes_trace![opt] "[{(t.elapsedSuccessful + t.elapsedFailed).printAsMillis} / {t.elapsedSuccessful.printAsMillis} / {t.elapsedFailed.printAsMillis}] {n}"

end Stats


abbrev StatsRef := IO.Ref Stats

class MonadStats (m) extends MonadOptions m where
  modifyGetStats : (Stats → α × Stats) → m α
  getStats : m Stats :=
    modifyGetStats λ s => (s, s)
  modifyStats : (Stats → Stats) → m Unit :=
    λ f => modifyGetStats λ s => ((), f s)

export MonadStats (modifyGetStats getStats modifyStats)

instance [MonadStats m] : MonadStats (StateRefT' ω σ m) where
  modifyGetStats f := (modifyGetStats f : m _)
  getStats := (getStats : m _)
  modifyStats f := (modifyStats f : m _)

instance [MonadStats m] : MonadStats (ReaderT α m) where
  modifyGetStats f := (modifyGetStats f : m _)
  getStats := (getStats : m _)
  modifyStats f := (modifyStats f : m _)

instance [MonadOptions m] [MonadStateOf Stats m] : MonadStats m where
  modifyGetStats f := modifyGetThe Stats f
  getStats := getThe Stats
  modifyStats := modifyThe Stats

variable [Monad m]

@[inline, always_inline]
def enableStatsCollection [MonadOptions m] : m Bool :=
  coaes.collectStats.get <$> getOptions

@[inline, always_inline]
def enableStatsTracing [MonadOptions m] : m Bool :=
  TraceOption.stats.isEnabled

@[inline, always_inline]
def enableStatsFile [MonadOptions m] : m Bool := do
  return coaes.stats.file.get (← getOptions) != ""

@[inline, always_inline]
def enableStats [MonadOptions m] : m Bool :=
  enableStatsCollection <||> enableStatsTracing <||> enableStatsFile

variable [MonadStats m] [MonadLiftT BaseIO m]

@[inline, always_inline]
def profiling (recordStats : Stats → α → Nanos → Stats) (x : m α) : m α := do
  if ← enableStats then
    let (result, elapsed) ← time x
    modifyStats (recordStats · result elapsed)
    return result
  else
    x

@[inline, always_inline]
def profilingRuleSelection : m α → m α :=
  profiling λ stats _ elapsed =>
    { stats with ruleSelection := stats.ruleSelection + elapsed }

@[inline, always_inline]
def profilingRule (rule : DisplayRuleName) (wasSuccessful : α → Bool) :
    m α → m α :=
  profiling λ stats a elapsed =>
    let rp := { successful := wasSuccessful a, rule, elapsed }
    { stats with ruleStats := stats.ruleStats.push rp }

def modifyStatsIfEnabled (f : Stats → Stats) : m Unit := do
  if ← enableStats then
    modifyStats f

def recordScriptGenerated (x : ScriptGenerated) : m Unit := do
  modifyStatsIfEnabled ({ · with scriptGenerated := some x })

end CoAes
