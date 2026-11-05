module

public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMeasurement
public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundMeasurementProfiles
public import JanetCartan.Iteration.RevisedUniform.OriginalFinalCore
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMeasurementApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean

/-!
# Actual measured target term of the complete source

Apply the finite-moment estimate on the very same reference and common core
as `OriginalFinalCore.source_interval`. The global canonical measurement on
the original native history has no row index. Neither a measurement estimate
nor a successful mean iteration is an input. This is the target summand in
`new:eq:mean-source`, **not** the entire forcing or Main: the transported
leading continuum minus the sampled corrected background is also necessary.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalCompleteForcing

private theorem stage_two {S R₀ : ℝ} (h : 2 ≤ S) (k : S ≤ R₀) : 2 ≤ R₀ := h.trans k

end JanetCartan.PhysicalMean.OriginalCompleteForcing
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalCompleteForcingApplication
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate (withActualRow bodyAt)

private def ns := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def cm := `JanetCartan.PhysicalMean.OriginalCanonicalMeasurement
private def bg := `JanetCartan.PhysicalMean.OriginalBackgroundHermitian
private def meas := `JanetCartan.PhysicalMean.OriginalBackgroundMeasurementProfiles
private def graded := `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent
private def graph := `JanetCartan.PhysicalSampling.OriginalGraphResponse.B
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def finalCore := `JanetCartan.RevisedUniform.OriginalFinalCore
private def app (c : Name) (xs : Array Expr) := mkAppN (mkConst c) xs

private def save (short : Name) (p : Array Expr) (term target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p term)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "complete source {short}: missing dependencies {missing.toList}"
    if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasSorry then
      throwError "complete source {short}: late/implicit source or recovered proof"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ short
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The measured target summand on the original physical history and canonical measurement. Only given target data and the finite-order numerical/metric defect conditions are used (new:eq:mean-source; main:lem:smoothing). This is not the complete source or Main."
  logInfo m!"same-history complete source component {short}: native{p.size}"

/- The numerical coefficient bounds are known for *every* row and their
statement is row-free. Eliminate the original nonempty finite row index as in
the existing proof of commonC_smooth. No selected row becomes part of Cper. -/
run_cmd liftTermElabM <| withTransparency .reducible <| withActualRow fun d => do
  let p := d.parameters[:50].toArray
  let n := d.raw13[0]!
  let cell := mkApp (mkConst `JanetCartan.fundamentalCell) n
  let hp := app (meas ++ `physical_profile) (d.parameters.push cell)
  let tp ← inferType hp
  unless tp.isAppOfArity `JanetCartan.HasDerivativeProfile 11 do
    throwError "measured target: not the existing global physical coefficient profile"
  let pa := tp.getAppArgs
  let hc ← bodyAt (cm ++ `Cper_smooth) p
  unless hc.isAppOfArity (cm ++ `nativeMeasurement_smooth) 6 do
    throwError "measured target: existing measurement no longer has its exact support box"
  let h := hc.getAppArgs
  let C := app (bg ++ `commonC) p
  unless h[1]! == C do throwError "measured target: changed common physical C"
  let A := app (meas ++ `CM) p[:44].toArray
  unless pa[10]! == A do throwError "measured target: changed original static CM"
  let v := app (ns ++ `measurement_cell_profile)
    #[n,pa[8]!,C,h[3]!,pa[9]!,A,h[4]!,h[5]!,hp]
  let rawPeriod := app (cm ++ `nativeMeasurement) #[n,C]
  let period := app (cm ++ `Cper) p
  let target := (← inferType v).replace fun e => if e == rawPeriod then some period else none
  unless (target.find? (· == period)).isSome && !(target.containsFVar d.row.fvarId!) do
    throwError "measured target: Cper lost or a particular row entered the common bound"
  let old ← bodyAt (bg ++ `commonC_smooth) p
  unless old.isAppOfArity ``Nonempty.elim 4 do throwError "measured target: missing original row nonemptiness"
  let args := old.getAppArgs
  let proof := mkAppN old.getAppFn #[args[0]!,target,args[2]!,← mkLambdaFVars #[d.row] v]
  save `measurement_profile p proof target

/- Recover the SAME regular source interval as the actual full-response
producer, including its original chosen bare frame rather than an unrelated
extra allowance. Eliminate the temporary color by the checked static spine. -/
run_cmd liftTermElabM <| withTransparency .reducible <| withActualRow fun d => do
  let p := d.parameters[:50].toArray
  let n := d.raw13[0]!
  let t ← inferType (app (graded ++ `uncut_response_jets) d.parameters)
  let .forallE c ctype _ bi := t.consumeMData | throwError "measured target: missing original color domain"
  let regular25 ← withLocalDeclNoLocalInstanceUpdate c bi ctype fun col => do
    let ht ← inferType (app (graded ++ `uncut_response_jets) (d.parameters.push col))
    let some g := ht.find? (·.isAppOfArity graph 42) |
      throwError "measured target: changed actual full-response graph"
    if g.hasLooseBVars then throwError "measured target: graph depends on a later jet"
    let gt := (← instantiateForall (← getConstInfo graph).type g.getAppArgs[:37].toArray).consumeMData
    let .forallE _ reached _ _ := gt | throwError "measured target: graph reach is not the original binder"
    unless reached.isAppOfArity ``LE.le 4 do throwError "measured target: changed original graph reach"
    let S := reached.getAppArgs[2]!
    unless S.isAppOfArity (reg ++ `Graph.S) 34 do
      throwError "measured target: expected the ORIGINAL graph threshold, got {S.getAppFn}"
    let fixed := S.getAppArgs
    let ref := fixed[:23].toArray ++ #[fixed[25]!,app (reg ++ `Graph.regular_scale) fixed[:27].toArray]
    for a in ref do
      if a.containsFVar col.fvarId! || a.containsFVar d.row.fvarId! || a.hasLooseBVars then
        throwError "measured target: a row/color entered the reference"
      for late in p[44:50] do
        if a.containsFVar late.fvarId! then throwError "measured target: scale/history entered the fixed reference"
    return ref
  let D := app (finalCore ++ `Dsmoothing) regular25[:23].toArray
  let G := app (reg ++ `Gref) regular25
  let hp := app (ns ++ `measurement_profile) p
  let tp ← inferType hp
  unless tp.isAppOfArity `JanetCartan.HasDerivativeProfile 11 do throwError "measured target: changed common Cper profile"
  let fixed := p[:44].toArray
  let S := app (graded ++ `S) fixed
  let two := app ``JanetCartan.PhysicalMean.OriginalCompleteForcing.stage_two #[S,p[44]!,app (graded ++ `hS) fixed,p[45]!]
  let v := app (ns ++ `measure_normalized_history)
    #[n,D,G,app (meas ++ `CM) fixed,app (meas ++ `CM_nonneg) fixed,p[44]!,two,p[46]!,p[47]!,
      tp.getAppArgs[8]!,app (cm ++ `Cper) p,app (cm ++ `Cper_smooth) p,hp]
  let t ← inferType v
  let namedCore := app (finalCore ++ `D) regular25[:23].toArray
  let rawCore := app `JanetCartan.LocalDomain.core #[D,n]
  let t := t.replace fun e => if e == rawCore then some namedCore else none
  unless (t.find? (· == G)).isSome && (t.find? (· == namedCore)).isSome &&
      (t.find? (·.isAppOf `JanetCartan.PhysicalSmoothing.normalizedSource)).isSome do
    throwError "measured target: missing genuine common core, finite-moment tensor, or reference"
  save `measured_target p v t

end JanetCartan.PhysicalMean.OriginalCompleteForcingApplication
end
