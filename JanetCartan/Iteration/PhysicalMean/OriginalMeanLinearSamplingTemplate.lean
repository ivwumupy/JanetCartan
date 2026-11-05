module
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSelection
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.PeriodicComparison
public import JanetCartan.Iteration.PhysicalMean.OriginalPeriodicBackgroundTemplate
public meta import JanetCartan.Iteration.PhysicalMean.OriginalPeriodicBackgroundTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearEstimates
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearEstimatesTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCurrent
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearEstimatesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSelectionApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularity
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWavesTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
public meta import Lean
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSelectionApplication
public meta import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearEstimatesTemplate
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCurrentApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
public meta import JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
public meta import JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularity
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWavesTemplate
public meta import JanetCartan.Iteration.PhysicalBackground.CanonicalDensity

/-! # The original SAME-event finite sampled normal

The unchanged native50 selected event supplies the full-prefix deviation.
Normalize the summed family once, then identify its full-angular outer raw
normal using zero-safe identities; the baseline, source and inverse are never
resampled. Consumer: app:ch_mean_pairs:eq:mean-stage-normal-errors. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate
open SeparatedSampling Sampling Sampling.Realization SamplingKernelBounds
open PeriodicLocalL2 ContinuumRow OriginalMeanLinearEstimatesTemplate
open scoped BigOperators

/-- The exact common-event inequality transferred once to the real normalized
output. No extra row count and no second event are used. -/
theorem normalized_event {n p : ℕ} {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (B : ℝ) (ψ : I → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (ξ : I → ShiftSpace p B h)
    (T : I → (Fin 3 → Fin (p+1)) → Point → E →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (auxiliary : OutputL2 n →L[ℝ] OutputL2 n) {t : ℝ}
    (hevent : ‖familyDeviation p B ψ w h T ξ‖ ≤ t) :
    ‖(auxiliary+∑ i, normalizedComplexNormal (patchMeanNormal p B (ψ i) w h (T i)))-
      (auxiliary+∑ i, normalizedComplexNormal
        (patchSampleNormal p B (ψ i) w h (T i) (extendedShift (ξ i))))‖ ≤
      (4*((((2*Real.pi)^(-(n : ℝ)/2))⁻¹)^2))*t := by
  apply normalized_sampling_error
  simpa only [familyDeviation, Finset.sum_sub_distrib] using hevent

end JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate
open Lean Meta Elab Command
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def profiles := `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current
private def bodyAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo n).value? (allowOpaque := true)
    | throwError "actual sampling normal: missing producer {n}"
  return (value.beta xs).headBeta

elab "publish_original_inner_sampling_normal" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.sampling_deviation
  forallBoundedTelescope (← getConstInfo source).type (some 50) fun xs _ => do
    let hevent := app source xs
    let eventType ← inferType hevent
    let deviation := eventType.getAppArgs[2]!.appArg!
    unless deviation.isAppOfArity `JanetCartan.Sampling.Realization.familyDeviation 17 do
      throwError "actual sampling normal: original deviation17 changed"
    let da := deviation.getAppArgs
    logInfo m!"exact selected-event tolerance: {eventType.getAppArgs[3]!}"
    let transport ← inferType (app
      `JanetCartan.PhysicalMean.OriginalMeanLinearEstimates.global_transport xs)
    let corrected := transport.getAppArgs[2]!.appArg!.getAppArgs[5]!
    let auxiliary := corrected.getAppArgs[4]!
    unless auxiliary.isAppOfArity `JanetCartan.CurrentMean.preparationAuxiliaryOutput 3 do
      throwError "actual sampling normal: unchanged global auxiliary missing"
    let n := auxiliary.getAppArgs[0]!
    let name := `JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate.normalized_event
    let info ← getConstInfo name
    unless (← inferType da[3]!).isAppOfArity ``Fintype 1 do
      throwError "actual sampling normal: original finite-index instance changed"
    let proof := mkAppN (mkConst name (info.levelParams.map (fun _ => .zero)))
      (#[n,da[10]!,da[0]!,da[1]!,da[3]!,da[4]!,da[5]!,da[6]!,
        da[11]!,da[12]!,da[13]!,da[14]!,da[16]!,da[15]!,auxiliary,eventType.getAppArgs[3]!,hevent])
    let type ← instantiateMVars (← mkForallFVars xs (← inferType proof))
    let value ← instantiateMVars (← mkLambdaFVars xs proof)
    let env ← getEnv
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
        throwError "actual sampling normal: extra or unresolved input"
      let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
      unless missing.isEmpty do throwError "actual sampling normal: missing producers {missing.toList}"
    let name := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.inner_sampling_error
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
    logInfo "actual normalized native50 inner sampling error kernel accepted"
end JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate
end

@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate
open SeparatedSampling Sampling Sampling.Realization SamplingKernelBounds
open PeriodicLocalL2 ContinuumRow CanonicalRowComparison OriginalMeanLinearEstimatesTemplate
open scoped BigOperators

private theorem normalized_sum {n : ℕ} {I : Type*} [Fintype I]
    (E : I → EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n))) :
    normalizedComplexNormal (∑ i, E i) = ∑ i, normalizedComplexNormal (E i) := by
  ext1 v
  simp only [normalizedComplexNormal, transferOperator, realOutputCompression,
    ContinuousLinearMap.comp_apply, sum_apply, smul_apply,
    ContinuousLinearMap.coe_restrictScalars', map_sum, Finset.smul_sum]

/-- Transfer the literal full-angular outer row to the already selected inner
sample normal. The Fourier scalar is fixed, and no sample weight is divided by.
Consumer: actual native50 normal in app:ch_mean_pairs:eq:mean-stage-normal-errors. -/
theorem raw_normal_eq_sum_normalized_of_patch_eq {n p : ℕ} {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (B : ℝ) (ψ : I → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : I → Lattice → Point)
    (T : I → (Fin 3 → Fin (p+1)) → Point → E →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (S : I → EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (hμ : ∀ i : SampleIndex p B ψ w h U, 0 ≤ sampleWeight B ψ w h U i)
    (hpatch : ∀ i, patchSampleNormal p B (ψ i) w h (T i) (U i) = S i) :
    let A := CanonicalRow.weightedRow (sampleWeight B ψ w h U)
      (rawIntegralSampledComponent B ψ w h U T)
    A.comp A.adjoint = ∑ i, normalizedComplexNormal (S i) := by
  dsimp only
  rw [rawIntegral_sampled_weightedRow_normal,
    periodic_sampled_weightedRow_normal B ψ w h U T hμ]
  have hsum : (∑ i, patchSampleNormal p B (ψ i) w h (T i) (U i)) = ∑ i, S i :=
    Finset.sum_congr rfl (fun i _ => hpatch i)
  rw [hsum]
  exact normalized_sum S

end JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate
end
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate
open Lean Meta Elab Command
private partial def measuredDeviation (proof : Expr) : MetaM (Option Expr) := do
  let ty ← inferType proof
  if ty.isForall &&
      (ty.find? (·.isAppOfArity `JanetCartan.Sampling.Realization.familyDeviation 17)).isSome &&
      (ty.find? (·.isAppOfArity `JanetCartan.PhysicalSampling.OriginalJointEvent.measured_kernel 60)).isSome then
    return some proof
  unless ty.isAppOfArity ``And 2 do return none
  if let some found ← measuredDeviation (.proj ``And 0 proof) then return some found
  measuredDeviation (.proj ``And 1 proof)

elab "publish_original_selected_deviation" : command => liftTermElabM do
  let selected := `JanetCartan.PhysicalMean.OriginalCanonicalSelection.event
  forallBoundedTelescope (← getConstInfo selected).type (some 50) fun xs _ => do
    let hSelected := mkAppN (mkConst selected) xs
    let some all ← measuredDeviation hSelected
      | throwError "actual sample deviation: exact selected measured-prefix fact missing"
    let allType ← inferType all
    let second := allType.bindingBody!
    unless second.isForall do throwError "actual sample deviation: prefix premise changed"
    let cutBound := second.bindingDomain!
    unless cutBound.isAppOfArity ``LE.le 4 do throwError "actual sample deviation: original prefix ceiling changed"
    let J := cutBound.getAppArgs[3]!
    if J.hasLooseBVars then throwError "actual sample deviation: prefix ceiling depends on prefix variable"
    let hJ ← mkAppM ``le_refl #[J]
    let valueAt := mkAppN all #[J,hJ]
    let atType ← inferType valueAt
    let dev := atType.getAppArgs[2]!.appArg!
    unless dev.isAppOfArity `JanetCartan.Sampling.Realization.familyDeviation 17 do
      throwError "actual sample deviation: changed literal familyDeviation17"
    logInfo m!"actual deviation on fixed original J: {J.getAppFn}"
    for j in [10:17] do
      let e := dev.getAppArgs[j]!
      let head := if e.getAppFn.isConst then e.getAppFn.constName!.toString else "(lambda or variable)"
      logInfo m!"deviation argument {j}: {head}, argc={e.getAppNumArgs}"
    let type ← instantiateMVars (← mkForallFVars xs atType)
    let value ← instantiateMVars (← mkLambdaFVars xs valueAt)
    let env ← getEnv
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
        throwError "actual sample deviation: unresolved/extra premise"
      let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
      unless missing.isEmpty do throwError "actual sample deviation: missing producers {missing.toList}"
    let name := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.sampling_deviation
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
end JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate
end

@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate
open PeriodicLocalL2 ContinuumRow OriginalMeanLinearEstimatesTemplate
open scoped BigOperators

/-- Use the actual per-row kernel equality before the family sum; no norm or
cardinality loss occurs (app:ch_mean_pairs:eq:mean-stage-normal-errors). -/
theorem normalized_family_congr {n : ℕ} {I : Type*} [Fintype I]
    (auxiliary : OutputL2 n →L[ℝ] OutputL2 n)
    (E F : I → EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (h : ∀ i, E i = F i) :
    auxiliary + ∑ i, normalizedComplexNormal (E i) =
      auxiliary + ∑ i, normalizedComplexNormal (F i) := by
  congr 1
  exact Finset.sum_congr rfl (fun i _ => congrArg normalizedComplexNormal (h i))

/-- The unchanged sampling cost is static and nonnegative, with no inverse
sample weight (app:ch_mean_pairs:eq:mean-stage-normal-errors). -/
theorem normalized_sampling_factor_nonneg (n : ℕ) :
    0 ≤ 4*((((2*Real.pi)^(-(n : ℝ)/2))⁻¹)^2) :=
  mul_nonneg (by norm_num) (sq_nonneg _)

/-- Sum the actual positive comparison costs with the SAME fixed Fourier
normalization (app:ch_mean_pairs:eq:mean-stage-normal-errors). -/
theorem normalized_transport_factor_nonneg (n : ℕ) {I : Type*} [Fintype I]
    (C : I → ℝ) (hC : ∀ i, 0 < C i) :
    0 ≤ (4*((((2*Real.pi)^(-(n : ℝ)/2))⁻¹)^2))*(∑ i, C i) :=
  mul_nonneg (normalized_sampling_factor_nonneg n)
    (Finset.sum_nonneg fun i _ => (hC i).le)

end JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate
end

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate.OuterPatch
open Lean Meta Elab Command
private def rowNS := `JanetCartan.PhysicalMean.OriginalCanonicalRow
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def geometry (xs : Array Expr) : MetaM (Expr × Expr × Expr) := do
  let some body := (← getConstInfo (rowNS ++ `D)).value? (allowOpaque := true)
    | throwError "actual outer patch: missing original kernel D50"
  let dm := (body.beta xs).headBeta
  unless dm.isAppOfArity `JanetCartan.PhysicalSampling.OriginalJointEvent.measured_kernel 60 do
    throwError "actual outer patch: original measured kernel60 changed"
  let m := dm.getAppArgs
  let fixed := m[:46].toArray
  let rates := app `JanetCartan.PhysicalSampling.OriginalCommonStage.stage_rates
    (fixed ++ #[m[47]!,m[48]!,m[49]!])
  let h0 := app `JanetCartan.PhysicalSampling.OriginalCommonThreshold.T₀_ge_one fixed
  let hR ← mkAppM ``le_trans #[h0,.proj ``And 0 rates]
  let mesh ← mkAppM `JanetCartan.PhysicalSampling.OriginalBareEvent.mesh_bounds #[hR]
  let hw ← mkAppM `JanetCartan.PhysicalSampling.OriginalWindow.window_bounds #[m[45]!]
  return (hw,.proj ``And 0 mesh,.proj ``And 1 mesh)

elab "publish_original_outer_patch" : command => liftTermElabM do
  OriginalPeriodicBackgroundTemplate.withActualCanonicalSample fun xs _ si J _ hU event => do
    let eventType ← inferType event
    let some deviation := eventType.find?
        (·.isAppOfArity `JanetCartan.Sampling.Realization.familyDeviation 17)
      | throwError "actual outer patch: SAME measured event missing"
    let B := deviation.getAppArgs[11]!
    unless B.isAppOfArity `JanetCartan.PhysicalSampling.OriginalWeights.B 22 do
      throwError "actual outer patch: original sampler22 changed"
    let static := B.getAppArgs
    let I := si.getAppArgs[0]!
    let (hw,hh,hh1) ← geometry xs
    withLocalDeclD `i I fun i => do
      let D := app (rowNS ++ `D) (xs.push i)
      let hInner := app (rowNS ++ `normal_sample_actual)
        (xs ++ #[i,D,J,mkApp hU i,hw,hh,hh1])
      let it ← inferType hInner
      unless it.isAppOfArity ``Eq 3 do throwError "actual outer patch: original sample bridge changed"
      let left := it.getAppArgs[1]!
      unless left.isAppOfArity `JanetCartan.Sampling.Realization.patchSampleNormal 15 do
        throwError "actual outer patch: literal patch normal changed"
      let leftArgs := left.getAppArgs
      let hPrefix := app `JanetCartan.PhysicalMean.OriginalWeightBridge.Original.scalarKernel_prefix_factor
        (static ++ #[i,J,D,J])
      let hKernel ← forallBoundedTelescope (← inferType hPrefix) (some 1) fun c _ => do
        unless c.size == 1 do throwError "actual outer patch: scalar prefix color changed"
        let hPoint ← mkAppM ``funext #[mkApp hPrefix c[0]!]
        mkAppM ``funext #[← mkLambdaFVars c hPoint]
      let f ← withLocalDeclD `T (← inferType leftArgs[13]!) fun T =>
        mkLambdaFVars #[T] (mkAppN left.getAppFn (leftArgs.set! 13 T))
      let hOuter ← mkAppM ``congrArg #[f,hKernel]
      let proof ← mkAppM ``Eq.trans #[hOuter,hInner]
      let params := xs.push i
      let type ← instantiateMVars (← mkForallFVars params (← inferType proof))
      let value ← instantiateMVars (← mkLambdaFVars params proof)
      let env ← getEnv
      for e in #[type,value] do
        if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
          throwError "actual outer patch: extra or unresolved input"
        let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
        unless missing.isEmpty do throwError "actual outer patch: missing producers {missing.toList}"
      let name := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.outer_patch_eq_inner
      addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
      logInfo "actual outer scalar-kernel patch normal = SAME selected inner patch normal; native51 only"
end JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate.OuterPatch
end

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate.NormalIdentity
open Lean Meta Elab Command
private def rowNS := `JanetCartan.PhysicalMean.OriginalCanonicalRow
private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def bodyAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some body := (← getConstInfo n).value? (allowOpaque := true)
    | throwError "actual normal: missing producer {n}"
  return (body.beta xs).headBeta
private def save (key : Name) (xs : Array Expr) (term : Expr) (data := false)
    (target : Option Expr := none) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars xs
    (← match target with | none => inferType term | some ty => pure ty))
  let value ← instantiateMVars (← mkLambdaFVars xs term)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual normal {key}: unresolved or extra input"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual normal {key}: missing producers {missing.toList}"
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  logInfo m!"actual normal {key}: original{xs.size}"
  return app name xs

elab "publish_original_sampled_normal" : command => liftTermElabM do
  let patchSource := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.outer_patch_eq_inner
  forallBoundedTelescope (← getConstInfo patchSource).type (some 51) fun x _ => do
    let xs := x[:50].toArray
    let i := x[50]!
    let onePatch := app patchSource x
    let pt ← inferType onePatch
    let left := pt.getAppArgs[1]!
    let la := left.getAppArgs
    let S ← mkLambdaFVars #[i] pt.getAppArgs[2]!
    let T ← mkLambdaFVars #[i] la[13]!
    let ψ ← mkLambdaFVars #[i] la[10]!
    let U ← mkLambdaFVars #[i] la[14]!
    let hPatch ← mkLambdaFVars #[i] onePatch
    let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift xs
    let shiftArgs := xs.push shift
    let hWeight := app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.sample_weights_nonneg shiftArgs
    let hevent := app `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.sampling_deviation xs
    let et ← inferType hevent
    let da := et.getAppArgs[2]!.appArg!.getAppArgs
    let some kernel := pt.getAppArgs[2]!.find? (·.isAppOf
      `JanetCartan.Sampling.refinedKernelPrefix)
      | throwError "actual normal: original full kernel prefix missing"
    let J := kernel.getAppArgs[kernel.getAppNumArgs-2]!
    if J.hasLooseBVars then throwError "actual normal: prefix depends on a later sample coordinate"
    let rowArgs := shiftArgs.push J
    let A := app (rowNS ++ `A) rowArgs
    let weights := app (rowNS ++ `weights) shiftArgs
    let rawA ← bodyAt (rowNS ++ `A) rowArgs
    unless rawA.isAppOf `JanetCartan.CanonicalRowComparison.rawIntegralSampledComponent do
      throwError "actual normal: original raw-integral component changed"
    let some realIP ← rawA.getAppArgs.findM? (fun e => do
      let ty ← inferType e
      return ty.isAppOf ``InnerProductSpace && ty.getAppArgs[0]!.isConstOf ``Real)
      | throwError "actual normal: original real input structure missing"
    let some tower ← rawA.getAppArgs.findM? (fun e => do
      return (← inferType e).isAppOf ``IsScalarTower)
      | throwError "actual normal: original complex/real compatibility missing"
    let global ← inferType (app
      `JanetCartan.PhysicalMean.OriginalMeanLinearEstimates.global_transport xs)
    let aux := global.getAppArgs[2]!.appArg!.getAppArgs[5]!.getAppArgs[4]!
    let n := aux.getAppArgs[0]!
    let name := `JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate.raw_normal_eq_sum_normalized_of_patch_eq
    let arguments := #[n,la[8]!,← inferType i,la[0]!,da[3]!,la[2]!,la[3]!,realIP,tower,la[4]!,
      la[9]!,ψ,la[11]!,la[12]!,U,T,S,hWeight,hPatch]
    let info ← getConstInfo name
    let proof := mkAppN (mkConst name (info.levelParams.map (fun _ => .zero))) arguments
    let proofType ← zetaReduce (← inferType proof)
    let normal := proofType.getAppArgs[1]!
    let some rawRow := normal.find? (·.isAppOf `JanetCartan.CanonicalRow.weightedRow)
      | throwError "actual normal: unchanged weighted row missing"
    let wa := rawRow.getAppArgs
    let actualRow := mkAppN rawRow.getAppFn ((wa.set! (wa.size-2) weights).set! (wa.size-1) A)
    let target := proofType.replace fun e => if e == rawRow then some actualRow else none
    let hNormal ← save `sampled_normal_eq_inner xs proof false (some target)
    let hSampling := app `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.inner_sampling_error xs
    let st ← inferType hSampling
    let right := st.getAppArgs[2]!.appArg!.getAppArgs[5]!
    let sumSample := right.getAppArgs[5]!
    let normalEquality ← inferType hNormal
    let predicate ← withLocalDeclD `N (← inferType sumSample) fun N =>
      mkLambdaFVars #[N] (st.replace fun e => if e == sumSample then some N else none)
    let hCongr := mkAppN (mkConst ``congrArg [.succ .zero,.succ .zero])
      #[normalEquality.getAppArgs[0]!,mkSort .zero,normalEquality.getAppArgs[1]!,
        normalEquality.getAppArgs[2]!,predicate,hNormal]
    let ct ← inferType hCongr
    let final := mkAppN (mkConst ``Eq.mpr [.zero])
      #[ct.getAppArgs[1]!,ct.getAppArgs[2]!,hCongr,hSampling]
    discard <| save `actual_sampling_error xs final
    let actualNormal := right.replace fun e =>
      if e == sumSample then some normalEquality.getAppArgs[1]! else none
    discard <| save `sampledNormal xs actualNormal true
    let cost := st.getAppArgs[3]!.getAppArgs[4]!
    discard <| save `Csample xs[:44].toArray cost true
end JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate.NormalIdentity
end

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate.MeanParts
open PeriodicLocalL2 ContinuumRow OriginalMeanLinearEstimatesTemplate OriginalMeanLinearSamplingTemplate
open scoped BigOperators
/-- Finite-index instances do not choose different samples; both sums range
through the SAME index type and use the exact same pointwise means. -/
theorem normalized_family_congr_with_fintypes {n : ℕ} {I : Type*}
    (f g : Fintype I) (auxiliary other : OutputL2 n →L[ℝ] OutputL2 n)
    (E F : I → EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (haux : auxiliary = other) (h : ∀ i, E i = F i) :
    (letI := f; auxiliary+∑ i, normalizedComplexNormal (E i)) =
      (letI := g; other+∑ i, normalizedComplexNormal (F i)) := by
  have hfg : f = g := Subsingleton.elim _ _
  subst g
  subst other
  let := f
  exact normalized_family_congr auxiliary E F h
end JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate.MeanParts
end
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate.MeanParts
open Lean Meta Elab Command
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def save (key : Name) (xs : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars xs target)
  let value ← instantiateMVars (← mkLambdaFVars xs proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual mean component {key}: extra or unresolved input"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual mean component {key}: missing producers {missing.toList}"
  let name := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling ++ key
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  logInfo m!"actual mean component {key}: original{xs.size}"

elab "publish_original_global_mean_component " mode:num : command => liftTermElabM do
  let transportName := `JanetCartan.PhysicalMean.OriginalMeanLinearEstimates.global_transport
  forallBoundedTelescope (← getConstInfo transportName).type (some 50) fun xs _ => do
    let gt ← inferType (app transportName xs)
    let corrected := gt.getAppArgs[2]!.appArg!.getAppArgs[5]!
    let auxiliary := corrected.getAppArgs[4]!
    let sum := corrected.getAppArgs[5]!
    unless sum.isAppOfArity ``Finset.sum 5 do throwError "actual mean component: corrected family sum changed"
    let sample := app `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.inner_sampling_error xs
    let st ← inferType sample
    let eventCorrected := st.getAppArgs[2]!.appArg!.getAppArgs[4]!
    let eventAuxiliary := eventCorrected.getAppArgs[4]!
    let eventSum := eventCorrected.getAppArgs[5]!
    unless eventSum.isAppOfArity ``Finset.sum 5 do throwError "actual mean component: SAME event mean sum changed"
    if mode.getNat == 0 then
      lambdaTelescope sum.getAppArgs[4]! fun row term => do
        unless row.size == 1 do throwError "actual mean component: original row binder changed"
        let some mean := term.find? (·.isAppOfArity
          `JanetCartan.Sampling.Realization.patchMeanNormal 14)
          | throwError "actual mean component: corrected patch mean missing"
        let eventTerm := (mkApp eventSum.getAppArgs[4]! row[0]!).headBeta
        let some eventMean := eventTerm.find? (·.isAppOfArity
          `JanetCartan.Sampling.Realization.patchMeanNormal 14)
          | throwError "actual mean component: event patch mean missing"
        let kernelEq := app `JanetCartan.PhysicalMean.OriginalMeanLinearEstimates.corrected_kernel_eq_event
          (xs.push row[0]!)
        let ka := (← inferType kernelEq).getAppArgs
        unless (mean.find? (· == ka[1]!)).isSome do
          throwError "actual mean component: corrected kernel is not the checked kernel"
        let f ← withLocalDeclD `D ka[0]! fun D =>
          mkLambdaFVars #[D] (mean.replace fun e => if e == ka[1]! then some D else none)
        let proof := mkAppN (mkConst ``congrArg [.succ .zero,.succ .zero])
          #[ka[0]!,← inferType mean,ka[1]!,ka[2]!,f,kernelEq]
        let target := mkAppN (mkConst ``Eq [.succ .zero])
          #[← inferType mean,mean,eventMean]
        save `pointwise_corrected_eq_event (xs ++ row) proof target
    else if mode.getNat == 1 then
      unless auxiliary == eventAuxiliary do
        throwError "actual mean component: selected-event auxiliary is not literally global"
      let type ← inferType auxiliary
      let proof := mkAppN (mkConst ``Eq.refl [.succ .zero]) #[type,auxiliary]
      let target := mkAppN (mkConst ``Eq [.succ .zero]) #[type,auxiliary,eventAuxiliary]
      save `auxiliary_eq_event xs proof target
    else throwError "actual mean component: unknown component"
end JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate.MeanParts
end
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate.MeanJoin
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def save (key : Name) (xs : Array Expr) (proof : Expr)
    (target : Option Expr := none) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars xs
    (← match target with | some t => pure t | none => inferType proof))
  let value ← instantiateMVars (← mkLambdaFVars xs proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual global sample {key}: extra or unresolved input"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual global sample {key}: missing producers {missing.toList}"
  let name := root ++ key
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  logInfo m!"actual global sample {key}: original{xs.size}"
  return app name xs

elab "publish_original_global_mean_join" : command => liftTermElabM do
  let transportName := `JanetCartan.PhysicalMean.OriginalMeanLinearEstimates.global_transport
  forallBoundedTelescope (← getConstInfo transportName).type (some 50) fun xs _ => do
    let gt ← inferType (app transportName xs)
    let corrected := gt.getAppArgs[2]!.appArg!.getAppArgs[5]!
    let auxiliary := corrected.getAppArgs[4]!
    let sum := corrected.getAppArgs[5]!
    unless sum.isAppOfArity ``Finset.sum 5 do throwError "actual global sample: corrected family sum changed"
    let st ← inferType (app
      `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.inner_sampling_error xs)
    let eventCorrected := st.getAppArgs[2]!.appArg!.getAppArgs[4]!
    let eventAuxiliary := eventCorrected.getAppArgs[4]!
    let eventSum := eventCorrected.getAppArgs[5]!
    unless eventSum.isAppOfArity ``Finset.sum 5 do throwError "actual global sample: event family sum changed"
    let sa := sum.getAppArgs
    let ea := eventSum.getAppArgs
    unless sa[3]!.isAppOfArity ``Finset.univ 2 && ea[3]!.isAppOfArity ``Finset.univ 2 do
      throwError "actual global sample: original finite index enumeration changed"
    let (E,F,hFamily) ← lambdaTelescope sa[4]! fun row _ => do
      unless row.size == 1 do throwError "actual global sample: original row binder changed"
      let point := app (root ++ `pointwise_corrected_eq_event) (xs ++ row)
      let pa := (← inferType point).getAppArgs
      return (← mkLambdaFVars row pa[1]!,← mkLambdaFVars row pa[2]!,← mkLambdaFVars row point)
    let haux := app (root ++ `auxiliary_eq_event) xs
    let n := auxiliary.getAppArgs[0]!
    let name := `JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate.MeanParts.normalized_family_congr_with_fintypes
    let info ← getConstInfo name
    let proof := mkAppN (mkConst name (info.levelParams.map (fun _ => .zero)))
      #[n,sa[0]!,sa[3]!.getAppArgs[1]!,ea[3]!.getAppArgs[1]!,
        auxiliary,eventAuxiliary,E,F,haux,hFamily]
    let target := mkAppN (mkConst ``Eq [.succ .zero])
      #[← inferType corrected,corrected,eventCorrected]
    discard <| save `global_corrected_eq_event xs proof (some target)

elab "publish_original_global_sampling_error" : command => liftTermElabM do
  let source := root ++ `global_corrected_eq_event
  forallBoundedTelescope (← getConstInfo source).type (some 50) fun xs _ => do
    let meanEq := app source xs
    let ma := (← inferType meanEq).getAppArgs
    let sampling := app
      `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.actual_sampling_error xs
    let st ← inferType sampling
    let oldMean := st.getAppArgs[2]!.appArg!.getAppArgs[4]!
    let predicate ← withLocalDeclD `M ma[0]! fun M =>
      mkLambdaFVars #[M] (st.replace fun e => if e == oldMean then some M else none)
    let eq := mkAppN (mkConst ``congrArg [.succ .zero,.succ .zero])
      #[ma[0]!,mkSort .zero,ma[1]!,ma[2]!,predicate,meanEq]
    let qa := (← inferType eq).getAppArgs
    let proof := mkAppN (mkConst ``Eq.mpr [.zero]) #[qa[1]!,qa[2]!,eq,sampling]
    discard <| save `sampling_error xs proof
end JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate.MeanJoin
end
