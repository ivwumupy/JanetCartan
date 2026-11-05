module
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearProfiles
public import JanetCartan.Iteration.PhysicalSampling.Probability
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCurrent
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredKernelsApplication
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowTemplate
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredKernelsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearComparisonTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCurrent
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearProfilesTemplate
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
public meta import Lean
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCurrentApplication
public meta import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
public meta import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearComparisonTemplate
public meta import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearProfilesTemplate
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

/-! # Actual original mean normal estimates

The corrected kernels and event are the SAME native50 data. The continuum
normal uses the ONE global native39 inverse and the paper's fixed K=Lambda.
No per-row inverse, new shift, or desired linear estimate is a premise.
Consumer: app:ch_mean_pairs:eq:mean-stage-normal-errors. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearEstimatesTemplate
open PeriodicLocalL2 ContinuumRow
open scoped BigOperators

variable {n : ℕ}
local notation "cF" => ((2 * Real.pi) ^ (-(n : ℝ) / 2))

/-- Exact raw-integral Fourier normalization, with both real quadratures.
Consumer: the SAME event's sampled-normal error in
`app:ch_mean_pairs:eq:mean-stage-normal-errors`. -/
def normalizedComplexNormal
    (E : EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n))) : OutputL2 n →L[ℝ] OutputL2 n :=
  (cF⁻¹)^2 • transferOperator ((4 : ℝ) • realOutputCompression E)

private theorem normalizedComplexNormal_sub
    (E F : EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n))) :
    normalizedComplexNormal (E-F) = normalizedComplexNormal E-normalizedComplexNormal F := by
  simp only [normalizedComplexNormal, realOutputCompression_sub, smul_sub,
    transferOperator, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

private theorem normalizedComplexNormal_sum {ι : Type*} [Fintype ι]
    (E : ι → EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n))) :
    normalizedComplexNormal (∑ i, E i) = ∑ i, normalizedComplexNormal (E i) := by
  ext1 u
  simp only [normalizedComplexNormal, transferOperator, realOutputCompression,
    ContinuousLinearMap.comp_apply, sum_apply,
    smul_apply, ContinuousLinearMap.coe_restrictScalars',
    map_sum, Finset.smul_sum]

private theorem normalizedComplexNormal_norm_le
    (E : EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n))) :
    ‖normalizedComplexNormal E‖ ≤ (4*(cF⁻¹)^2)*‖E‖ := by
  rw [normalizedComplexNormal, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (cF⁻¹)^2 * ‖(4 : ℝ) • realOutputCompression E‖ :=
      mul_le_mul_of_nonneg_left (norm_transferOperator_le _) (sq_nonneg _)
    _ = (cF⁻¹)^2 * (4*‖realOutputCompression E‖) := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    _ ≤ (cF⁻¹)^2 * (4*‖E‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (realOutputCompression_norm_le E) (by norm_num))
        (sq_nonneg _)
    _ = _ := by ring

/-- Apply the original one-event deviation after summing, not separately by row;
there is no loss of a row-count factor or second sample. -/
theorem normalized_sampling_error {ι : Type*} [Fintype ι]
    (auxiliary : OutputL2 n →L[ℝ] OutputL2 n)
    (E S : ι → EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n))) {t : ℝ}
    (hevent : ‖(∑ i, S i)-(∑ i, E i)‖ ≤ t) :
    ‖(auxiliary+∑ i, normalizedComplexNormal (E i))-
      (auxiliary+∑ i, normalizedComplexNormal (S i))‖ ≤ (4*(cF⁻¹)^2)*t := by
  rw [add_sub_add_left_eq_sub, ← normalizedComplexNormal_sum,
    ← normalizedComplexNormal_sum, ← normalizedComplexNormal_sub]
  exact (normalizedComplexNormal_norm_le _).trans
    (mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hevent)
      (mul_nonneg (by norm_num) (sq_nonneg _)))

/-- The literal transport rate pays the mesh denominator exactly; no false
`h*T≤1` restriction is used. -/
theorem original_transport_factor {R : ℝ} (hR : 0 < R) :
    (R^carrierExponent)⁻¹ * R^fineExponent / R^(-separationExponent) =
      R^(-((31 : ℝ)/640)) := by
  rw [div_eq_mul_inv, ← Real.rpow_neg hR.le, ← Real.rpow_neg hR.le,
    ← Real.rpow_add hR, ← Real.rpow_add hR]
  congr 1
  norm_num [carrierExponent, fineExponent, meanSlack, separationExponent]

/-- Keep the actual sampling exponent omega and its static coefficient.
Consumer: the coefficient-preserving finite Picard recurrence, with no stronger
sampling event or assumption that a fixed coefficient is at most one. -/
theorem original_normal_error_decay {R Ct Cs γ : ℝ} (hR : 1 ≤ R)
    (hCt : 0 ≤ Ct) (hγ : 0 < γ) :
    ((Ct*(R^carrierExponent)⁻¹*R^fineExponent/R^(-separationExponent)+
      Cs*R^(-((3 : ℝ)/512)))*γ⁻¹) ≤
      ((Ct+Cs)*γ⁻¹)*R^(-((3 : ℝ)/512)) := by
  have rate : Ct*(R^carrierExponent)⁻¹*R^fineExponent/R^(-separationExponent) ≤
      Ct*R^(-((3 : ℝ)/512)) := by
    calc
      _ = Ct*((R^carrierExponent)⁻¹*R^fineExponent/R^(-separationExponent)) := by ring
      _ = Ct*R^(-((31 : ℝ)/640)) := by
        rw [original_transport_factor (zero_lt_one.trans_le hR)]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hR (by norm_num)) hCt
  calc
    _ ≤ (Ct*R^(-((3 : ℝ)/512))+Cs*R^(-((3 : ℝ)/512)))*γ⁻¹ :=
      mul_le_mul_of_nonneg_right (add_le_add rate le_rfl) (inv_nonneg.mpr hγ.le)
    _ = _ := by ring

end JanetCartan.PhysicalMean.OriginalMeanLinearEstimatesTemplate
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearEstimatesTemplate
open Lean Meta Elab Command

private def comparisonNS := `JanetCartan.PhysicalMean.OriginalMeanLinearComparison
private def profilesNS := `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles
private def estimatesNS := `JanetCartan.PhysicalMean.OriginalMeanLinearEstimates
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def bodyAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some body := (← getConstInfo n).value? (allowOpaque := true)
    | throwError "original mean estimates: missing producer {n}"
  return (body.beta xs).headBeta
private def save (short : Name) (xs : Array Expr) (term : Expr) (data := false)
    (target : Option Expr := none) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars xs
    (← match target with | none => inferType term | some t => pure t))
  let value ← instantiateMVars (← mkLambdaFVars xs term)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "original mean estimates {short}: extra or unresolved input"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "original mean estimates {short}: missing producer constants {missing.toList}"
  let name := estimatesNS ++ short
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe})
      (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual original native50 mean estimate on the SAME global native39 inverse, original continuum carriers and unchanged measured family; no new history, rate, source, sample or normal-estimate premise (app:ch_mean_pairs:eq:mean-stage-normal-errors)."
  logInfo m!"actual original mean {short}: {xs.size} original inputs"
  return app name xs

/-- Root-beta the saved comparison, never replay its coefficient or response
construction. The corrected kernel is the SAME measured-family D50. -/
elab "construct_original_mean_estimate " mode:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (comparisonNS ++ `comparison)).type (some 51) fun x _ => do
    unless x.size == 51 do throwError "original mean estimates: comparison native51 changed"
    let xs := x[:50].toArray
    let i := x[50]!
    let comparison := app (comparisonNS ++ `comparison) x
    let complex ← mkAppM ``And.left #[comparison]
    let ct ← inferType complex
    unless ct.isAppOfArity ``LE.le 4 do throwError "original mean estimates: comparison inequality changed"
    let mean := ct.getAppArgs[2]!.appArg!.getAppArgs[4]!
    let rhs := ct.getAppArgs[3]!
    if mode.getNat == 0 || mode.getNat == 1 then
      let some kernel := mean.find? (·.isAppOf `JanetCartan.CanonicalRowComparison.correctedColoredCrossBandData)
        | throwError "original mean estimates: corrected kernel missing"
      let actual := app `JanetCartan.PhysicalMean.OriginalCanonicalRow.D x
      if mode.getNat == 0 then
        discard <| save `corrected_kernel_eq_event x (← mkEqRefl kernel) false
          (some (← mkEq kernel actual))
      else
        let hKernel := app (estimatesNS ++ `corrected_kernel_eq_event) x
        let f ← withLocalDeclD `D (← inferType kernel) fun D =>
          mkLambdaFVars #[D] (mean.replace fun e => if e == kernel then some D else none)
        let equality ← mkAppM ``congrArg #[f,hKernel]
        let eventMean := mean.replace fun e => if e == kernel then some actual else none
        discard <| save `correctedMean_eq_event_mean x equality false
          (some (← mkEq (app (comparisonNS ++ `correctedMean) x) eventMean))
    else if mode.getNat == 2 then
      let B := mean.getAppArgs[9]!
      unless B.isAppOfArity `JanetCartan.PhysicalSampling.OriginalWeights.B 22 do
        throwError "original mean estimates: original sampler22 changed"
      let sampler := B.getAppArgs
      let current ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalCurrent.Q0 xs
      unless current.isAppOfArity (profilesNS ++ `Current.Q0) 39 do
        throwError "original mean estimates: global row-free native39 changed"
      let native := current.getAppArgs
      let base := #[sampler[0]!,sampler[2]!,sampler[1]!] ++ sampler[3:22].toArray
      let original := base ++ native[21:39].toArray
      let h := rhs.getAppArgs[5]!
      let num := rhs.getAppArgs[4]!
      let K := num.getAppArgs[5]!
      let inner := num.getAppArgs[4]!
      let lam := inner.getAppArgs[5]!.appArg!
      let cost := inner.getAppArgs[4]!
      let J := app `JanetCartan.RawInputPartition.cutoffCount #[K]
      let hJ ← mkAppM ``le_refl #[J]
      let prefixArgs := original ++ #[J,K,hJ]
      let E ← mkLambdaFVars #[i] mean
      let C ← mkLambdaFVars #[i] cost
      let hCompare ← mkLambdaFVars #[i] (← mkAppM ``And.right #[comparison])
      let applied := app (profilesNS ++ `Transport.of_original_comparisons)
        (prefixArgs ++ #[E,C,lam,K,h,hCompare])
      discard <| save `global_transport xs applied
    else if mode.getNat == 3 || mode.getNat == 4 then
      let hGlobal := app (estimatesNS ++ `global_transport) xs
      let ty ← inferType hGlobal
      unless ty.isAppOfArity ``LE.le 4 do throwError "original mean estimates: global transport changed"
      if mode.getNat == 3 then
        let difference := ty.getAppArgs[2]!.appArg!
        discard <| save `correctedNormal xs difference.getAppArgs[5]! true
      else
        let bound := ty.getAppArgs[3]!
        let cost := bound.getAppArgs[4]!.getAppArgs[4]!.getAppArgs[4]!
        discard <| save `Ctransport xs[:44].toArray cost true
    else throwError "original mean estimates: unknown publication stage"

end JanetCartan.PhysicalMean.OriginalMeanLinearEstimatesTemplate
end
