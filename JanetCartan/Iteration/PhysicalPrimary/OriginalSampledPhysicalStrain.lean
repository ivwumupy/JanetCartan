module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalSynthesis
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.CompletionAssembly.PrimaryStrain
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampleBudgets
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActualTemplate
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
import all JanetCartan.Iteration.PhysicalSampling.OriginalWeights
public meta import Lean

/-! The physical original primary strain aggregation for main:eq:primary-strain.
The same-field complex strain bound remains the explicit quantitative producer;
this implication does not supply source/angular rapid decay. The amplitude is
exactly the revised one, and the conclusion is on the physical cutoff core. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] noncomputable section
open Set Metric
open scoped ContDiff BigOperators Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalSourcePhysicalStrainApplication
open UniformStep SeparatedSampling CanonicalRowComparison
private theorem explicit_amplitude_strain_le {n N : ℕ} {ι : Type*} [Fintype ι]
    (D : LocalDomain) (F : Euclidean n → Euclidean N)
    (b : ℝ) (hb : 0 ≤ b) (μ : ι → ℝ)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) (D.chart n))
    (E S : ℝ) (hE : 0 ≤ E) (hS : (∑ i, Real.sqrt (μ i)) ≤ S)
    (hstrain : ∀ i, ∀ x ∈ D.core n, ‖WKB.complexLinearizedMetric F (Z i) x‖ ≤ E)
    (x : Euclidean n) (hx : x ∈ D.core n) :
    ‖linearizedMetric F (cutSampledPrimary D b μ Z hZ) x‖ ≤
      (b * Real.sqrt 2) * (S * E) := by
  rw [linearizedMetric_cutSampledPrimary_eq D F b μ Z hZ hx]
  have hxc : x ∈ D.chart n := closedBall_subset_ball D.coreRadius_lt_chartRadius hx
  have hcx (i : ι) : DifferentiableAt ℝ (Z i) x :=
    ((hZ i).contDiffAt (isOpen_ball.mem_nhds hxc)).differentiableAt (by simp)
  have hr (i : ι) : DifferentiableAt ℝ (euclideanRealPart ∘ Z i) x :=
    euclideanRealPart.differentiableAt.comp x (hcx i)
  have hreal (i : ι) : ‖linearizedMetric F (euclideanRealPart ∘ Z i) x‖ ≤ E :=
    (norm_linearizedMetric_realPart_le F (hcx i)).trans (hstrain i x hx)
  have hsum : ‖∑ i, Real.sqrt (μ i) • linearizedMetric F (euclideanRealPart ∘ Z i) x‖ ≤
      (∑ i, Real.sqrt (μ i)) * E :=
    WeightedFamily.norm_sum_weight_smul_le_of_norm_le Finset.univ
      (fun i ↦ Real.sqrt (μ i)) (fun _ _ ↦ Real.sqrt_nonneg _)
      (fun i ↦ linearizedMetric F (euclideanRealPart ∘ Z i) x) (fun i _ ↦ hreal i)
  rw [sampledPrimary,
    linearizedMetric_smul_apply (DifferentiableAt.sum
      (fun i _ ↦ (hr i).const_smul (Real.sqrt (μ i)))),
    linearizedMetric_sum_smul_apply Finset.univ _ _ (fun i _ ↦ hr i),
    norm_smul, Real.norm_of_nonneg (mul_nonneg hb (Real.sqrt_nonneg 2))]
  exact mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_right hS hE))
    (mul_nonneg hb (Real.sqrt_nonneg 2))
private theorem cut_original_sample_revised_strain_le {n N : ℕ} {G : Type*} [Fintype G]
    (D : LocalDomain) (F : Euclidean n → Euclidean N) (p : ℕ)
    {B W : ℝ} (hB : 0 ≤ B) {P : G → ℝ}
    {weights : G → Point → ℝ} {w : ℝ → ℝ}
    (hw : WindowBounds p w W) (hweights : ∀ a, PatchBounds (weights a) B (P a))
    {R δ C : ℝ} (hR : 1 ≤ R) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (shifts : G → Lattice → Point)
    (Z : SampleIndex p B weights w (R ^ (-separationExponent)) shifts →
      Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) (D.chart n)) (q : ℕ)
    (hstrain : ∀ i, ∀ x ∈ D.core n, ‖WKB.complexLinearizedMetric F (Z i) x‖ ≤
      C * (R ^ carrierExponent) ^ (-(q : ℝ))) :
    let Ccount := (Fintype.card G : ℝ) * countConstant p B
    let Cmass := countConstant p B * ((∑ a, P a) * W ^ 3)
    let μ := sampleWeight (p := p) B weights w (R ^ (-separationExponent)) shifts
    ∀ x ∈ D.core n,
      ‖linearizedMetric F
        (cutSampledPrimary D (δ * R ^ RevisedScales.forcingExponent n) μ Z hZ) x‖ ≤
      ((Real.sqrt 2 * C * Real.sqrt (Ccount * Cmass)) * δ) *
        (R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2) *
          (R ^ carrierExponent) ^ (-(q : ℝ))) := by
  intro Ccount Cmass μ x hx
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hbudget := sampled_weight_budgets_originalScale p hB hw hweights hR shifts
  have h := explicit_amplitude_strain_le D F (δ * R ^ RevisedScales.forcingExponent n)
    (mul_nonneg hδ (Real.rpow_nonneg hRpos.le _)) μ Z hZ
    (C * (R ^ carrierExponent) ^ (-(q : ℝ)))
    (Real.sqrt (Ccount * Cmass) * R ^ ((1 + samplingSlack) / 2))
    (mul_nonneg hC (Real.rpow_nonneg (Real.rpow_nonneg hRpos.le _) _))
    hbudget.2.2.2.2.2.2 hstrain x hx
  exact h.trans_eq (by rw [Real.rpow_add hRpos]; ring)
end JanetCartan.PhysicalPrimary.OriginalSourcePhysicalStrainApplication
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSourcePhysicalStrainApplication
open Lean Meta Elab Command
private def ns := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
private def app (name : Name) (args : Array Expr) := mkAppN (mkConst name) args
private partial def head (e : Expr) : Expr :=
  match e.headBeta with
  | .letE _ _ v b _ => head (b.instantiate1 v)
  | .mdata _ b => head b
  | e => e
private def exactType (value : Expr) : MetaM Expr := do
  let info ← getConstInfo value.getAppFn.constName!
  let mut type := info.type.instantiateLevelParams info.levelParams value.getAppFn.constLevels!
  for arg in value.getAppArgs do
    let .forallE _ _ rest _ := head type | throwError "changed literal primary signature"
    type := rest.instantiate1 arg
  return head type
private def termWith (vars : List (Name × Expr)) (code : String) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code)
private def save (key : Name) (params : Array Expr) (value target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual primary strain: unresolved expression at {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  liftM <| IO.eprintln s!"checking actual source primary strain {key} / {params.size}"
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  logInfo m!"checked actual source primary strain {key} / {params.size}"
run_cmd liftTermElabM do
  OriginalSampledPhysicalProfilesQuantitativeTemplate.withActualSelectedSourceWave
    fun params _ _ _ _ native _ => do
      let source := params[:52].toArray
      let index ← inferType params[52]!
      unless index.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
        throwError "changed actual sample index"
      let s := index.getAppArgs
      let rows := s[0]!
      unless rows.isAppOfArity `JanetCartan.PhysicalSampling.OriginalWeights.Index 22 do
        throwError "changed original row index"
      let cube ← getConstInfo `JanetCartan.PhysicalSampling.OriginalWeights.exists_cube
      let some cubeProof := cube.value? (allowOpaque := true) | throwError "missing original finite cube"
      let cubeProof := head (cubeProof.beta rows.getAppArgs)
      unless cubeProof.isAppOfArity `JanetCartan.PhysicalSampling.exists_finite_original_carrier_weight_bounds 5 do
        throwError "changed original finite cube signature"
      let finite := cubeProof.getAppArgs[1]!
      let wave := app (ns ++ `selectedSourceCombinedWave) params
      let smooth := app (ns ++ `selectedSourceCombinedWave_smooth) params
      let smType ← exactType smooth
      unless smType.isAppOfArity ``ContDiffOn 11 do throwError "changed original smoothness"
      let chart := smType.getAppArgs[10]!
      unless chart.isAppOfArity `JanetCartan.LocalDomain.chart 2 do throwError "lost Dsmooth chart"
      let D := chart.getAppArgs[0]!
      let n := chart.getAppArgs[1]!
      let N := smType.getAppArgs[5]!.getAppArgs[1]!.appArg!
      let Z ← mkLambdaFVars #[params[52]!] wave
      let hZ ← mkLambdaFVars #[params[52]!] smooth
      let same := app `JanetCartan.PhysicalSampling.OriginalGraphResponse.same_finite_map native[:42].toArray
      let F := (← exactType same).getAppArgs[2]!
      unless F.isAppOf `JanetCartan.RevisedGlobal.finiteMap do throwError "not SAME native finiteMap"
      if (← mkLambdaFVars params[:50].toArray F).hasFVar then
        throwError "physical finiteMap depends on sample or source"
      let outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
      let p := rows.getAppArgs
      unless s[2]! == app (outer ++ `B) p && s[3]! == app (outer ++ `ψ) p do
        throwError "changed original outer weights"
      let hB ← termWith [(`hB,app (outer ++ `hB) p)] "(le_of_lt hB)"
      let hweights := app (outer ++ `patchBounds) p
      let mut positiveOrder : Option Expr := none
      for x in params[:44].toArray do
        let t ← inferType x
        if t.isAppOfArity ``LT.lt 4 && t.getAppArgs[0]! == mkConst ``Nat && t.getAppArgs[3]! == s[1]! then
          if ← isDefEq t.getAppArgs[2]! (mkNatLit 0) then positiveOrder := some x
      let some hp := positiveOrder | throwError "missing original p positivity"
      let hw := app `JanetCartan.PhysicalSampling.OriginalWindow.window_bounds #[s[1]!,hp]
      let one ← mkNumeral (mkConst ``Real) 1
      let P ← withLocalDeclNoLocalInstanceUpdate `row .default rows fun row => mkLambdaFVars #[row] one
      let rates := app `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelope.stage_rates params[:50].toArray
      let R := (← inferType (Expr.proj ``And 0 rates)).appArg!
      let hS := app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS params[:44].toArray
      let hR ← termWith [(`R0,params[44]!),(`j,params[46]!),(`hS,hS),(`hR,params[45]!)]
        "(by have h : (1 : ℝ) ≤ R0 := le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_trans hS hR); exact h.trans (JanetCartan.le_historyScale h j))"
      withLocalDeclNoLocalInstanceUpdate `Cstrain .default (mkConst ``Real) fun C => do
        let hCt ← termWith [(`C,C)] "(0 ≤ C)"
        withLocalDeclNoLocalInstanceUpdate `hCstrain .default hCt fun hC => do
          withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q => do
            withLocalDeclNoLocalInstanceUpdate `δ .default (mkConst ``Real) fun δ => do
              let hδt ← termWith [(`δ,δ)] "(0 ≤ δ)"
              withLocalDeclNoLocalInstanceUpdate `hδ .default hδt fun hδ => do
                let proof := mkAppN (mkConst ``cut_original_sample_revised_strain_le [.zero])
                  #[n,N,rows,finite,D,F,s[1]!,s[2]!,one,hB,P,s[3]!,s[4]!,hw,hweights,
                    R,δ,C,hR,hδ,hC,s[6]!,Z,hZ,q]
                let result ← exactType proof
                let some raw := result.find? (·.isAppOfArity `JanetCartan.PhysicalPrimary.cutSampledPrimary 9) |
                  throwError "missing literal physical aggregate in result"
                let named := app (ns ++ `selectedSourcePrimary) (source.push δ)
                let target := result.replace fun e => if e == raw then some named else none
                unless target.getUsedConstantsAsSet.contains (ns ++ `selectedSourcePrimary) do
                  throwError "actual primary was not retained"
                let all := source[:44].toArray ++ #[C,hC,q] ++ source[44:].toArray ++ #[δ,hδ]
                save `selectedSourcePrimary_strain_of_complex_strain all proof target
end JanetCartan.PhysicalPrimary.OriginalSourcePhysicalStrainApplication
end
#print axioms JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourcePrimary_strain_of_complex_strain
