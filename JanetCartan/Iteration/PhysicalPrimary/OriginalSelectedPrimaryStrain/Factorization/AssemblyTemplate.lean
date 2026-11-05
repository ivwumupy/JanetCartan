module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.Algebra
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPrimaryStrainMaskData
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteBaselineIdentity
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourcePlateau
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianSupportTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# The original raw primary differential at its ordinary carrier

On the unchanged source chart, the derivative of the original pre-response
wave is the ordinary carrier times the unscaled raw baseline plus the whole
raw source field.  The proof joins the actual baseline differential, the
complete annular raw identity and the original unweighted adjoint input.
The same observation is removed on its existing plateau.  The carrier is
then written at the original history frequency and `group_phase`, without
doubling it (`main:eq:primary-strain`, `app:ch_regular:eq:source-tail`).

The independently proved phase and raw amplitude profiles are the consumers
of this identity.  No first-mask or corrected-strain estimate is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization

private theorem combine_on_source_chart {n N : ℕ}
    (X : Set (Euclidean n)) (hX : IsOpen X)
    (Z W : Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ : ContDiffOn ℝ ∞ Z X) (hW : ContDiffOn ℝ ∞ W X)
    (x : Euclidean n) (hx : x ∈ X)
    (B D : Matrix (Fin N) (Fin n) ℂ) (θ ψ : ℝ)
    (hψ : ψ = 1)
    (hB : OriginalPrimaryStrainMaskData.rawJacobian Z x =
      Complex.exp (Complex.I * (θ : ℂ)) • B)
    (hD : ψ • (Complex.exp (-Complex.I * (θ : ℂ)) •
      OriginalPrimaryStrainMaskData.rawJacobian W x) = D) :
    OriginalPrimaryStrainMaskData.rawJacobian (Z+W) x =
      Complex.exp (Complex.I * (θ : ℂ)) • (B+D) := by
  have hw := (hW.contDiffAt (hX.mem_nhds hx)).differentiableAt (by simp)
  have hz := (hZ.contDiffAt (hX.mem_nhds hx)).differentiableAt (by simp)
  exact raw_sum_derivative_factor Z W x B D θ ψ hz hw hψ hB hD

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization
end

public meta section

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.Template

open Lean Meta Elab Command
open SourceTemplate (app bodyAt typeAt save withSource)

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization
private def baseline := `JanetCartan.PhysicalPrimary.OriginalRawBaselineProfiles
private def actual := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Actual
private def completePhase := `JanetCartan.PhysicalPairs.OriginalCompleteAmplitude.phase

elab "identify_original_raw_primary_factor " mode:num : command => liftTermElabM do
  unless mode.getNat < 3 do throwError "raw primary factorization: unknown mode"
  withSource fun d => do
    if mode.getNat == 2 then
      let statement := app (root ++ `raw_factor_statement) d.params
      forallBoundedTelescope (← typeAt statement) (some 2) fun point _ => do
        unless point.size == 2 do throwError "raw primary factorization: final source tail changed"
        let all := d.params ++ point
        let sourceProof := app (root ++ `observed_raw_angular_eq_source) all
        let proof := app (root ++ `raw_factor_of_source) (all.push sourceProof)
        save `raw_factor_on_source_chart all proof (app (root ++ `raw_factor_statement) all)
      return
    let ordinary := app completePhase d.sourceArgs
    let oldBase := app
      `JanetCartan.PhysicalPairs.OriginalCompleteBaselineIdentity.baseline_eq_actual_baseline d.sourceArgs
    let bt ← typeAt oldBase
    unless bt.isAppOfArity ``Eq 3 && bt.getAppArgs[2]!.isAppOfArity
        `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.baselineAmplitude 56 do
      throwError "raw primary factorization: original outer baseline data changed"
    let bp := bt.getAppArgs[2]!.getAppArgs
    let index ← inferType d.sample
    unless index.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
      throwError "raw primary factorization: original sample type changed"
    let hweight := mkAppN
      (mkConst `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.original_sample_weight_ne_zero [.zero])
      (index.getAppArgs.push d.sample)
    let baseFactor := app (actual ++ `baseline_factor) (bp.push hweight)
    forallBoundedTelescope (← typeAt baseFactor) (some 2) fun point _ => do
      unless point.size == 2 do throwError "raw primary factorization: original point/chart tail changed"
      let x := point[0]!
      let originalBaseFactor := mkAppN baseFactor point
      let baseIdentity := app (actual ++ `baseline_eq_original_raw) (bp.push hweight)
      let bit ← typeAt baseIdentity
      unless bit.isAppOfArity ``Eq 3 do
        throwError "raw primary factorization: original raw baseline identity changed"
      let jacobian ← withLocalDeclD `Z bit.getAppArgs[0]! fun Z =>
        mkLambdaFVars #[Z]
          (app `JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.rawJacobian #[d.n,d.N,Z,x])
      let originalBaseType ← bodyAt
        (app (actual ++ `baseline_factor_statement) (bp ++ #[hweight] ++ point))
      let ba := bit.getAppArgs
      let sameJacobian := mkAppN (mkConst ``congrArg [.one,.one])
        #[ba[0]!,originalBaseType.getAppArgs[0]!,ba[1]!,ba[2]!,jacobian,baseIdentity]
      let sameType ← typeAt sameJacobian
      unless sameType.isAppOfArity ``Eq 3 && originalBaseType.isAppOfArity ``Eq 3 do
        throwError "raw primary factorization: original baseline equations changed"
      let sj := sameType.getAppArgs
      let reversed := mkAppN (mkConst ``Eq.symm sameType.getAppFn.constLevels!)
        #[sj[0]!,sj[1]!,sj[2]!,sameJacobian]
      let hB := mkAppN (mkConst ``Eq.trans sameType.getAppFn.constLevels!)
        #[sj[0]!,sj[2]!,sj[1]!,originalBaseType.getAppArgs[2]!,reversed,originalBaseFactor]
      let sourceStatement := app (root ++ `observed_raw_angular_statement) (d.params ++ point)
      withLocalDeclD `hSource sourceStatement fun hD => do
        let dt ← bodyAt (app (root ++ `observed_raw_angular_statement) (d.params ++ point))
        unless dt.isAppOfArity ``Eq 3 && dt.getAppArgs[1]!.isAppOfArity ``HSMul.hSMul 6 do
          throwError "raw primary factorization: original observation changed"
        let ψ := dt.getAppArgs[1]!.getAppArgs[4]!
        let B := mkApp (app (baseline ++ `baseline) bp) x
        let D := mkApp (app `JanetCartan.PhysicalPrimary.OriginalRawSourceProfile.field d.params) x
        let plateau := app `JanetCartan.PhysicalPairs.OriginalSourcePlateau.germ_on_original_chart
          (d.chart.getAppArgs ++ point)
        let hone ← mkAppM ``Filter.EventuallyEq.eq_of_nhds #[plateau]
        let joined := app ``Factorization.combine_on_source_chart
          #[d.n,d.N,d.chart,app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart_open d.chart.getAppArgs,
            d.baseline,d.angularField,app (actual ++ `baseline_smooth_on_source) (bp.push hweight),
            app (root ++ `raw_angular_smooth) d.params,x,point[1]!,B,D,mkApp ordinary x,ψ,hone,hB,hD]
        let jt ← typeAt joined
        unless jt.isAppOfArity ``Eq 3 do
          throwError "raw primary factorization: actual sum factorization changed"
        let phaseIdentity := app (root ++ `phase_eq_original_carrier) (d.sourceArgs.push x)
        let pt ← bodyAt (app (root ++ `phase_statement) (d.sourceArgs.push x))
        let rhs := jt.getAppArgs[2]!
        let context ← withLocalDeclD `theta (mkConst ``Real) fun theta =>
          mkLambdaFVars #[theta] (rhs.replace fun e => if e == mkApp ordinary x then some theta else none)
        let pa := pt.getAppArgs
        let rotated := mkAppN (mkConst ``congrArg [.one,.one])
          #[pa[0]!,jt.getAppArgs[0]!,pa[1]!,pa[2]!,context,phaseIdentity]
        let rotatedType ← typeAt rotated
        unless rotatedType.isAppOfArity ``Eq 3 do
          throwError "raw primary factorization: original phase transport changed"
        let ja := jt.getAppArgs
        let proof := mkAppN (mkConst ``Eq.trans jt.getAppFn.constLevels!)
          #[ja[0]!,ja[1]!,ja[2]!,rotatedType.getAppArgs[2]!,joined,rotated]
        let lhs := app `JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.rawJacobian
          #[d.n,d.N,d.rawField,x]
        let target ← mkEq lhs (rhs.replace fun e =>
          if e == mkApp ordinary x then some pt.getAppArgs[2]! else none)
        let all := d.params ++ point
        if mode.getNat == 0 then
          save `raw_factor_statement all target (mkSort .zero) true
        else
          save `raw_factor_of_source (all.push hD) proof (app (root ++ `raw_factor_statement) all)
          addDocStringCore (root ++ `raw_factor_of_source)
            "Exact full raw primary factorization from the precise original angular source identity; the actual baseline, source-chart plateau, regularity and undoubled source phase are supplied internally. The final raw_factor_on_source_chart supplies the completed source producer, leaving no new premise (main:eq:primary-strain)."

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.Template
end

