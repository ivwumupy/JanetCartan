module

public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalMeasurementProfiles
public meta import Lean

/-!
# Actual global measurement profiles for the unscaled positive background

Read the SAME original native50 event through the checked actual95 row view.
The uncut mean's saved measurement proof is literally the original global
`OriginalMeasurement.at_reserve` producer. Retain its common prehistory budget,
its existing reached proof and its exact sampler reserve. In particular the
native event threshold already dominates the measurement threshold: no new
maximum, cap, event, current, cutoff, source or reference is selected.

Consumer: `HermitianCarrierPullback.exists_weighted_local_carrier_profiles`,
`app:ch_waves:eq:background-quadrature` and
`app:ch_mean_pairs:eq:comparison-input`. The full-parent amplitude and support
geometry are separate primitives; this module does not periodize C or claim Main.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalBackgroundMeasurementProfilesTemplate

private theorem budget_nonneg (C : ℕ → ℝ) (h : ∀ j, 0 < C j) : ∀ j, 0 ≤ C j :=
  fun j ↦ (h j).le

private theorem threshold_refl (s : ℝ) : s ≤ s := le_refl s

private theorem threshold_trans (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  hab.trans hbc

end JanetCartan.PhysicalMean.OriginalBackgroundMeasurementProfilesTemplate
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalBackgroundMeasurementProfilesTemplate
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate (ActualRow withActualRow bodyAt)

private def ns := `JanetCartan.PhysicalMean.OriginalBackgroundMeasurementProfiles
private def bg := `JanetCartan.PhysicalMean.OriginalBackgroundHermitian
private def producer := `JanetCartan.PhysicalNormalInverse.OriginalMeasurement
private def app (n : Name) (a : Array Expr) := mkAppN (mkConst n) a
private def tail (h : Expr) (j : Nat) := Nat.repeat (fun e ↦ Expr.proj ``And 1 e) j h
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (tail h j)

private def save (key : Name) (params : Array Expr) (value : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar ||
      type.hasLevelMVar || value.hasLevelMVar || type.hasLooseBVars || value.hasLooseBVars ||
      type.hasSorry || value.hasSorry then
    throwError "actual background measurement: late/open or recovered field {key}"
  let name := ns ++ key
  liftM <| IO.eprintln s!"actual background measurement: checking {key}/{params.size}"
  liftM <| (← IO.getStderr).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual original common measurement primitive for the unscaled positive Hermitian background: same native event/current, exact sampler reserve and coefficient scale, common prehistory budget, and proved native threshold dominance. No profile-success premise or new physical choice (app:ch_waves:eq:background-quadrature; app:ch_mean_pairs:eq:comparison-input)."
  liftM <| IO.eprintln s!"actual background measurement: passed {key}/{params.size}"
  liftM <| (← IO.getStderr).flush
  logInfo m!"checked actual background measurement {key}/{params.size}"

/-- Read the already-supplied actual producer, not a profile-success assumption.
Only the saved application root is opened; its current and measurement are kept. -/
private def actualProducer (d : ActualRow) : MetaM Expr := do
  let some lower := d.mean70[64]!.find? (·.isAppOfArity
      `JanetCartan.PhysicalNormalInverse.OriginalComparisonCurrent.measurement_at_reserve 51) |
    throwError "actual background measurement: saved mean64 lost original reserve51"
  let h ← bodyAt lower.getAppFn.constName! lower.getAppArgs
  unless h.isAppOfArity (producer ++ `at_reserve) 40 do
    throwError "actual background measurement: saved producer is not exact at_reserve40"
  if h.hasLooseBVars then throwError "actual background measurement: a later sample entered producer"
  let a := h.getAppArgs
  unless a[31]! == d.parameters[44]! && a[33]! == d.parameters[46]! do
    throwError "actual background measurement: changed R/history stage"
  unless a[38]! == d.mean70[61]! do
    throwError "actual background measurement: changed sampler reserve"
  let smooth ← inferType (part h 0)
  unless smooth.isAppOf `ContDiff && smooth.appArg! == d.mean70[37]! do
    throwError "actual background measurement: changed actual n/Q/mu/hmu"
  return h

/-- Instantiate the original measurement producer on actual95 C. Static fields
close over original44, before R/history/row/color; profiles quantify arbitrary K.
The threshold dominance proof specializes the existing reached proof at eventS,
not a presumed comparison of two independently chosen numerical thresholds. -/
elab "retain_actual_background_measurement " which:num : command => liftTermElabM <|
    withTransparency .reducible <| withActualRow fun d => do
  let h ← actualProducer d
  let a := h.getAppArgs
  let static := d.parameters[:44].toArray
  let rowStatic := static.push d.row
  let fixed := a[:31].toArray
  let C := d.mean70[37]!
  unless C.isAppOfArity `JanetCartan.Sampling.canonicalSamplingMeasurement 4 do
    throwError "actual background measurement: not literal canonicalSamplingMeasurement4"
  let CM := app (producer ++ `Budgets.Cmeasure) fixed
  let positive := app (producer ++ `Budgets.positive) fixed
  let S := app (producer ++ `S) fixed
  for late in d.parameters[44:51] do
    if CM.containsFVar late.fvarId! || S.containsFVar late.fvarId! then
      throwError "actual background measurement: common budget/threshold acquired a late input"
  match which.getNat with
  | 0 => save `CM static CM true
  | 1 => save `CM_positive static positive
  | 2 => save `CM_nonneg static (app ``budget_nonneg #[CM,positive])
  | 3 => save `measurementS static S true
  | 4 => save `measurementS_ge_two static (app (producer ++ `hS) fixed)
  | 5 =>
    let reached ← inferType d.parameters[45]!
    unless reached.isAppOfArity ``LE.le 4 do
      throwError "actual background measurement: changed original event reached proof"
    let eventS := reached.getAppArgs[2]!
    unless eventS.isAppOfArity `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.S 44 do
      throwError "actual background measurement: different native event threshold"
    let proof := a[32]!.replaceFVars #[d.parameters[44]!,d.parameters[45]!]
      #[eventS,app ``threshold_refl #[eventS]]
    let target := mkAppN reached.getAppFn
      ((reached.getAppArgs.set! 2 (app (ns ++ `measurementS) static)).set! 3 eventS)
    save `measurementS_le_eventS rowStatic proof false (some target)
  | 6 =>
    let reached ← inferType d.parameters[45]!
    unless reached.isAppOfArity ``LE.le 4 do
      throwError "actual background measurement: changed original numerical reach"
    let eventS := reached.getAppArgs[2]!
    let proof := app ``threshold_trans #[app (ns ++ `measurementS) static,eventS,d.parameters[44]!,
      app (ns ++ `measurementS_le_eventS) rowStatic,d.parameters[45]!]
    save `measurement_reached d.parameters proof
  | 7 => save `reserve static a[39]!
  | 8 =>
    let namedC := app (bg ++ `C) d.parameters
    save `C_eq_native_measurement d.parameters (← mkEqRefl C) false (some (← mkEq namedC C))
  | 9 =>
    let t ← inferType (part h 0)
    let target := mkAppN t.getAppFn (t.getAppArgs.set! (t.getAppNumArgs-1) (app (bg ++ `C) d.parameters))
    save `smooth d.parameters (app (bg ++ `commonC_smooth) d.parameters[:50].toArray)
      false (some target)
  | 10 | 11 =>
    let a := (a.set! 32 (app (ns ++ `measurement_reached) d.parameters)).set! 39
      (app (ns ++ `reserve) static)
    let h := app (producer ++ `at_reserve) a
    let source := if which.getNat == 10 then part h 1 else tail h 2
    let sourceType ← inferType source
    unless sourceType.isForall do throwError "actual background measurement: missing arbitrary set"
    withLocalDeclNoLocalInstanceUpdate `K .default sourceType.bindingDomain! fun K => do
      let k := #[K]
      let proof := mkAppN source k
      let t ← inferType proof
      unless t.isAppOfArity `JanetCartan.HasDerivativeProfile 11 do
        throwError "actual background measurement: changed arbitrary-set profile11"
      let q := t.getAppArgs
      unless q[8]! == d.mean70[61]! do
        throwError "actual background measurement: altered mean reserve"
      unless q[9]! == d.mean70[60]! do
        throwError "actual background measurement: altered coefficient scale"
      unless q[10]! == CM do throwError "actual background measurement: altered static measurement budget"
      let namedC := app (bg ++ `C) d.parameters
      let f := q[7]!.replace fun e ↦ if e == C then some namedC else none
      let q := ((q.set! 7 f).set! 8 d.mean70[61]!).set! 9 d.mean70[60]!
      let q := q.set! 10 (app (ns ++ `CM) static)
      save (if which.getNat == 10 then `physical_profile else `joint_profile) d.parameters
        (← mkLambdaFVars k proof) false (some (← mkForallFVars k (mkAppN t.getAppFn q)))
  | _ => throwError "actual background measurement: unknown publication"

end JanetCartan.PhysicalMean.OriginalBackgroundMeasurementProfilesTemplate
end
