module

public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticApplication
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourceQuadratic
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSelection
public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundMeasurementProfiles
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeTesterBudgets
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputHilbert.Multiplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActual
import all JanetCartan.Iteration.PhysicalMean.OriginalMeasuredHermitianProfiles
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianSupportTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitian
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCurrentApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearProfilesTemplate
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
# Realize the original whole-annular quadratic primitives

The original correction cutoff, full finite-rate phase, fixed Fourier scalar,
original sample weights and the ONE selected event are preserved. These are
actual inputs to `fixedSourceQuadratic_low_bound` and its source-only sibling;
there is no second event, assumed annular identity, or output estimate
(`app:ch_mean_pairs:eq:block-bilinear`, `app:ch_waves:eq:sampling-prefix-normal`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual
open RawInputPartition RawInputRealization PhysicalForwardMean NormalComparison

/-- Only the fixed Fourier scalar in the original mask is compensated. -/
theorem forwardNormalization_cancel (n : ℕ) :
    (((2 * Real.pi) ^ (-((n : ℝ) / 2)) : ℝ) : ℂ) * forwardNormalization n = 1 := by
  have h : (2 * Real.pi) ^ (-((n : ℝ) / 2)) ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  simp only [forwardNormalization, neg_div, ← Complex.ofReal_mul, mul_inv_cancel₀ h, Complex.ofReal_one]

/-- Rewrite the SAME whole annular sum, including the zero angular and
observation branches. No summand is estimated or discarded. -/
theorem full_annuli_in_forward_coordinates {n N J : ℕ}
    (a : ℝ) (ψ : Euclidean n → ℝ) (z : Euclidean 3) (ζ : Euclidean (n-1)) (τ : ℝ)
    (d : Euclidean (n-1) → ℝ)
    (θ : Euclidean n → Euclidean (n-1) → ℝ)
    (φ : RefinedIndex J × Euclidean (n-1) → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean (n-1) → Matrix (Fin N) (Fin n) ℂ)
    (B : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → Matrix (Fin N) (Fin n) ℂ)
    (x : Euclidean n) (w : RefinedInput n J)
    (hφ : a ≠ 0 → ψ x ≠ 0 → ∀ j η, η ∈ annulus n (refinedRadius j) → φ (j,η) x = θ x η)
    (hB : a ≠ 0 → ψ x ≠ 0 → ∀ (j : RefinedIndex J) η, η ∈ annulus n (refinedRadius j) →
      B (x,z,ζ+τ • η) = A x (ζ+τ • η)) :
    a • (ψ x • (∑ j : RefinedIndex J,
      (∫ η, ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand (fun η ↦ (d η : ℂ)) j.1.val η * w j η) •
        (Complex.exp (Complex.I * (θ x η : ℝ)) • A x (ζ+τ • η))
        ∂annularMeasure n (refinedRadius j) : Matrix (Fin N) (Fin n) ℂ))) =
    ∑ j : RefinedIndex J, (∫ η, ((fun b c ↦ physicalForwardKernel (fun η ↦ φ (j,η))
      (fun η ↦ a * singleBareScalarMask d (j,η) * Real.sqrt ‖η‖)
      (forwardSlice ψ B z ζ τ b c) x η * w j η) : Matrix (Fin N) (Fin n) ℂ)
      ∂annularMeasure n (refinedRadius j) : Matrix (Fin N) (Fin n) ℂ) := by
  classical
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_smul, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_annulus n (refinedRadius j))] with η hη
  ext b c
  simp only [physicalForwardKernel, sampledMomentKernel, star_star, oscillatoryFactor, one_mul,
    forwardSlice, observedForwardAmplitude, weightedRadialBand, singleBareScalarMask,
    Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
  by_cases ha : a = 0
  · simp only [ha, Complex.ofReal_zero, zero_mul]
  by_cases hψ : ψ x = 0
  · simp only [hψ, Complex.ofReal_zero, zero_mul, mul_zero]
  rw [hφ ha hψ j η hη, hB ha hψ j η hη]
  linear_combination (norm := ring_nf) -(a:ℂ) * ψ x * (Real.sqrt ‖η‖ : ℂ) * d η *
    (radialBand n j.1.val η : ℂ) * w j η * Complex.exp (Complex.I * (θ x η : ℝ)) *
    (A x (ζ+τ • η)) b c * forwardNormalization_cancel n

open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts Sampling MeasuredAmplitude LeadingWave.FullModulation
open RawPrimary.MaskProfiles ContinuumRow

/-- The SAME original κ plateau controls both the base carrier and its actual
finite-rate shift, so both retained phase extensions equal the raw phase. -/
theorem retained_coordinates_on_original_annuli {e N J : ℕ} {P : Patch (e+1)}
    {U : Set (Euclidean (e+1))} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (Q : {q : Euclidean (e+1) → Fin (e+1) → MetricTensor (e+1) // ContDiffOn ℝ ∞ q U ∧
      cNorm (closedBall (0 : Euclidean (e+1)) T.data.localReference.stateRadius) 6
        (q - fun _ ↦ cubeStress (e+1)) < T.family.threshold})
    (z₀ Z Zraw : Euclidean 3) (heq : Zraw = Z) {ρ : ℝ} (hρ : 0 < ρ) (τ : ℝ)
    (a : ℝ) (ψ : Euclidean (e+1) → ℝ) {K : Set (Euclidean (e+1))} (hψK : tsupport ψ ⊆ K)
    {ηb : Euclidean (e+1-1)} {r : ℝ} (hηb : ηb ≠ 0) (hr : 0 < r)
    (A : Euclidean (e+1) × (Euclidean 3 × Euclidean (e+1-1)) → Matrix (Fin N) (Fin (e+1)) ℂ)
    (κ : Euclidean (e+1) × (Euclidean 3 × Euclidean (e+1-1)) → ℝ)
    {Ω : Set (Euclidean (e+1) × (Euclidean 3 × Euclidean (e+1-1)))}
    (hs : tsupport κ ⊆ Ω) (hphase : ∀ w ∈ Ω, (w.1,w.2.2) ∈ phaseDomain T)
    (hgraph : a ≠ 0 → (Zraw,T.reference.spatialPatch Zraw) ∈
      closedBall (z₀,T.reference.spatialPatch z₀) (ρ/4))
    (hκ : a ≠ 0 → ∀ x ∈ K, ∀ q : Euclidean (e+1-1), ‖q‖ ≤ ρ/4 →
      κ (x,Zraw,T.reference.spatialPatch Zraw+q) = 1)
    (hshift : ∀ (j : RefinedIndex J) {η}, η ∈ annulus (e+1) (refinedRadius j) → ‖τ • η‖ ≤ ρ/4)
    (x : Euclidean (e+1)) (w : RefinedInput (e+1) J) :
    a • (ψ x • (∑ j : RefinedIndex J,
      (∫ η, ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand
        (detectorMask (originalConicDetector hηb hr) (fun ξ ↦ FixedCutoffs.highFrequency ‖ξ‖)) j.1.val η * w j η) •
        (Complex.exp (Complex.I * (rawPrimaryPhaseDifference (LeadingWave.FullModulation.phase T Q)
          (T.reference.spatialPatch Zraw) τ x η : ℝ)) • A (x,Zraw,T.reference.spatialPatch Zraw+τ • η))
        ∂annularMeasure (e+1) (refinedRadius j) : Matrix (Fin N) (Fin (e+1)) ℂ))) =
    ∑ j : RefinedIndex J, (∫ η, ((fun b c ↦ physicalForwardKernel
      (fun η ↦ singleRetainedForwardPhase T Q (0,z₀,T.reference.spatialPatch z₀) hρ τ Z (j,η))
      (fun η ↦ a * singleBareScalarMask (originalForwardDetector hηb hr) (j,η) * Real.sqrt ‖η‖)
      (forwardSlice ψ (fun p ↦ κ p • A p) Z (T.reference.spatialPatch Z) τ b c) x η * w j η) :
        Matrix (Fin N) (Fin (e+1)) ℂ) ∂annularMeasure (e+1) (refinedRadius j) : Matrix (Fin N) (Fin (e+1)) ℂ) := by
  subst Zraw
  have hd : (fun η ↦ (originalForwardDetector hηb hr η : ℂ)) =
      detectorMask (originalConicDetector hηb hr) (fun ξ ↦ FixedCutoffs.highFrequency ‖ξ‖) :=
    funext (ofReal_originalForwardDetector hηb hr)
  rw [← hd]
  apply full_annuli_in_forward_coordinates a ψ Z (T.reference.spatialPatch Z) τ
    (originalForwardDetector hηb hr) _ _ (fun y ξ ↦ A (y,Z,ξ)) _ x w
  · intro ha hψ j η hη
    have hK := hψK (subset_tsupport _ hψ)
    have hz : Z ∈ closedBall z₀ ρ := by
      have h := hgraph ha
      rw [← closedBall_prod_same] at h
      exact closedBall_subset_closedBall (by linarith) h.1
    have h0 : κ (x,Z,T.reference.spatialPatch Z) = 1 := by
      simpa only [add_zero] using hκ ha x hK 0 (by rw [norm_zero]; positivity)
    have h1 := hκ ha x hK (τ • η) (hshift j hη)
    have h0' := hphase _ (hs (subset_tsupport _ (h0.trans_ne one_ne_zero)))
    have h1' := hphase _ (hs (subset_tsupport _ (h1.trans_ne one_ne_zero)))
    simp only [singleRetainedForwardPhase, extendedRetainedCarrier_eq T z₀ hρ hz,
      rawPrimaryPhaseDifference,extendedRetainedPhase_eq T Q h0',extendedRetainedPhase_eq T Q h1']
  · intro ha hψ j η hη
    rw [hκ ha x (hψK (subset_tsupport _ hψ)) (τ • η) (hshift j hη),one_smul]

private theorem coreInCarrierSupport {n : ℕ} {μ b : ℝ} (hμ : 0 < μ) (hb : 0 < b)
    (hmb : 6*μ < b) : closedBall (0 : Euclidean n) (4*μ) ⊆
      tsupport (ContinuumRow.FixedCutoffs.physical (n := n) hb 1) := by
  intro x hx
  have hi : x ∈ closedBall (0 : Euclidean n) (((1 : Fin 3).val+1 : ℝ)*b) := by
    apply closedBall_subset_closedBall _ hx
    norm_num
    linarith
  have he := interior_subset ((ContinuumRow.FixedCutoffs.physical_plateau hb 1) hi)
  exact subset_tsupport _ ((show ContinuumRow.FixedCutoffs.physical hb 1 x = 1 from he).trans_ne one_ne_zero)

/-- Restrict the SAME native L² input, not the physical output or measure. -/
theorem gate_native_tester {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure X) (gate : X → ℝ) (hgate : Measurable gate)
    (hbound : ∀ z, |gate z| ≤ 1)
    (φ : X → Euclidean n → ℝ) (m : X → ℝ) (χ : X → Euclidean n → ℂ)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hT : ∀ f, T f =ᵐ[volume] fun x ↦ ∫ z, sampledMomentKernel φ m χ x z * f z ∂μ) :
    ∃ P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)),
      ‖P‖ ≤ ‖T‖ ∧ ∀ f, P f =ᵐ[volume] fun x ↦
        ∫ z, sampledMomentKernel φ (fun z ↦ gate z * m z) χ x z * f z ∂μ := by
  let g : X → ℂ := fun z ↦ gate z
  have hg : AEStronglyMeasurable g μ :=
    (Complex.continuous_ofReal.measurable.comp hgate).aestronglyMeasurable
  have hb : ∀ᵐ z ∂μ, ‖g z‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun z ↦ by simpa only [g, Complex.norm_real, Real.norm_eq_abs] using hbound z)
  let M := RawInputHilbert.boundedMultiplier hg hb
  refine ⟨T.comp M, ?_, ?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left
        (RawInputHilbert.norm_boundedMultiplier_le hg zero_le_one hb) (norm_nonneg T)).trans_eq (mul_one _))
  · intro f
    filter_upwards [hT (M f)] with x hx
    change T (M f) x = _
    rw [hx]
    refine integral_congr_ae ?_
    filter_upwards [RawInputHilbert.boundedMultiplier_coeFn hg hb f] with z hz
    rw [hz]
    simp only [g, sampledMomentKernel, Complex.ofReal_mul]
    ring

open PhysicalSamplingShells
private theorem prefixGate_measurable {J : ℕ} (cut : ℕ) : Measurable (prefixGate (J := J) cut) :=
  (continuous_of_discreteTopology : Continuous (prefixGate (J := J) cut)).measurable
private theorem prefixGate_abs_le {J : ℕ} (cut : ℕ) (j : RefinedIndex J) : |prefixGate cut j| ≤ 1 := by
  by_cases h : j.1.val < cut <;> simp [prefixGate,h]

/-- The fixed prefix contracts the original individual bare tester. -/
theorem gate_individual {n J : ℕ} (cut : ℕ)
    (μ : Measure (RefinedIndex J × Euclidean (n-1)))
    (φ : RefinedIndex J × Euclidean (n-1) → Euclidean n → ℝ)
    (m : RefinedIndex J × Euclidean (n-1) → ℝ) (χ : RefinedIndex J × Euclidean (n-1) → Euclidean n → ℂ)
    (C : ℝ)
    (h : ∃ T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)), ‖T‖ ≤ C ∧
      ∀ f, T f =ᵐ[volume] fun x ↦ ∫ z, sampledMomentKernel φ m χ x z * f z ∂μ) :
    ∃ P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)), ‖P‖ ≤ C ∧
      ∀ f, P f =ᵐ[volume] fun x ↦ ∫ z, sampledMomentKernel φ (prefixMask cut m) χ x z * f z ∂μ := by
  obtain ⟨T,hC,hT⟩ := h
  obtain ⟨P,hP,e⟩ := gate_native_tester μ (fun z ↦ prefixGate cut z.1)
    ((prefixGate_measurable cut).comp measurable_fst) (fun z ↦ prefixGate_abs_le cut z.1) φ m χ T hT
  exact ⟨P,hP.trans hC,e⟩

/-- Preserve the original square-root mass and full half derivative. -/
theorem gate_aggregate {n J : ℕ} {ν : Type*} [MeasurableSpace ν] (cut : ℕ)
    (μ : Measure ((ν × RefinedIndex J) × Euclidean (n-1)))
    (φ : (ν × RefinedIndex J) × Euclidean (n-1) → Euclidean n → ℝ) (weight : ν → ℝ)
    (m : (ν × RefinedIndex J) × Euclidean (n-1) → ℝ)
    (χ : (ν × RefinedIndex J) × Euclidean (n-1) → Euclidean n → ℂ)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n))) (C : ℝ)
    (h : ‖T‖ ≤ C ∧ ∀ f, T f =ᵐ[volume] fun x ↦ ∫ z, sampledMomentKernel φ (originalWeightedHalfMask weight m) χ x z * f z ∂μ) :
    ∃ P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)), ‖P‖ ≤ C ∧
      ∀ f, P f =ᵐ[volume] fun x ↦ ∫ z, sampledMomentKernel φ
        (originalWeightedHalfMask weight (fun z ↦ prefixGate cut z.1.2 * m z)) χ x z * f z ∂μ := by
  obtain ⟨P,hP,e⟩ := gate_native_tester μ (fun z ↦ prefixGate cut z.1.2)
    ((prefixGate_measurable cut).comp (measurable_snd.comp measurable_fst))
    (fun z ↦ prefixGate_abs_le cut z.1.2) φ (originalWeightedHalfMask weight m) χ T h.2
  refine ⟨P,hP.trans h.1,?_⟩
  have eq : (fun z ↦ prefixGate cut z.1.2 * originalWeightedHalfMask weight m z) =
      originalWeightedHalfMask weight (fun z ↦ prefixGate cut z.1.2 * m z) := by
    ext z
    unfold originalWeightedHalfMask
    ring
  simpa only [eq] using e

private theorem physical_measurement_jets {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set (Euclidean n)) (C : Euclidean n → F)
    (CM : ℕ → ℝ) (T : ℝ) (hK : IsCompact K) (hc : ContDiff ℝ ∞ C) (hCM : ∀ j, 0 ≤ CM j)
    (hT : 1 ≤ T) (hp : HasDerivativeProfile K C (RawPrimary.SliceBounds.rawSliceParameterOrder n) T CM) :
    ∀ x ∈ K, ∀ j, ‖iteratedFDeriv ℝ j C x‖ ≤ CM j * T^(j-(2*(n/2+2)+(n/2+1))) := by
  intro x hx j
  apply (norm_iteratedFDeriv_le_cNorm hK (hc.of_le (by simp)) hx (le_refl j)).trans
  apply (hp j).trans
  apply mul_le_mul_of_nonneg_left _ (hCM j)
  apply pow_le_pow_right₀ hT
  unfold RawPrimary.SliceBounds.rawSliceParameterOrder RawPrimary.SliceBounds.rawSliceJetOrder
  omega

/-- Pack original discrete labels without differentiating sample indices. -/
theorem sampled_phase_continuous {ν : Type*} [TopologicalSpace ν] [DiscreteTopology ν] {n J : ℕ}
    (φ : ν → RefinedIndex J × Euclidean (n-1) → Euclidean n → ℝ)
    (hφ : ∀ i, Continuous (Function.uncurry (φ i))) :
    Continuous (Function.uncurry (fun z : (ν × RefinedIndex J) × Euclidean (n-1) ↦ φ z.1.1 (z.1.2,z.2))) := by
  have h : Continuous (fun p : ν × ((RefinedIndex J × Euclidean (n-1)) × Euclidean n) ↦
      φ p.1 p.2.1 p.2.2) := continuous_prod_of_discrete_left.mpr hφ
  exact h.comp (show Continuous (fun p : ((ν × RefinedIndex J) × Euclidean (n-1)) × Euclidean n ↦
    (p.1.1.1,((p.1.1.2,p.1.2),p.2))) from by fun_prop)

/-- Assemble the SAME original continuous frequency masks. -/
theorem sampled_mask_continuous {ν : Type*} [TopologicalSpace ν] [DiscreteTopology ν] {n J : ℕ}
    (m : ν → RefinedIndex J × Euclidean (n-1) → ℝ) (hm : ∀ i, Continuous (m i)) :
    Continuous (fun z : (ν × RefinedIndex J) × Euclidean (n-1) ↦ m z.1.1 (z.1.2,z.2)) := by
  have h : Continuous (fun p : ν × (RefinedIndex J × Euclidean (n-1)) ↦ m p.1 p.2) :=
    continuous_prod_of_discrete_left.mpr hm
  exact h.comp (show Continuous (fun p : (ν × RefinedIndex J) × Euclidean (n-1) ↦
    (p.1.1,(p.1.2,p.2))) from by fun_prop)

/-- Finiteness is used ONLY qualitatively for compact support, not to bound any
whole annular or sampled sum (`app:ch_mean_pairs:eq:block-bilinear`). -/
theorem sampled_mask_compact {ν : Type*} [Fintype ν] [TopologicalSpace ν] [DiscreteTopology ν] {n J : ℕ}
    (m : ν → RefinedIndex J × Euclidean (n-1) → ℝ) (hm : ∀ i, HasCompactSupport (m i)) :
    HasCompactSupport (fun z : (ν × RefinedIndex J) × Euclidean (n-1) ↦ m z.1.1 (z.1.2,z.2)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((isCompact_univ : IsCompact (univ : Set (ν × RefinedIndex J))).prod
      (isCompact_iUnion (fun i ↦ (hm i).image continuous_snd)))
  intro z hz
  exact ⟨mem_univ _,mem_iUnion.mpr ⟨z.1.1,⟨(z.1.2,z.2),subset_tsupport _ hz,rfl⟩⟩⟩

/-- Replace only row costs by their fixed prehistory envelopes. The actual
phase, mask, trade and all derivative orders remain unchanged. -/
theorem chart_budget_mono {n J : ℕ}
    {φ : RefinedIndex J × Euclidean (n-1) → Euclidean n → ℝ}
    {Φ : RefinedIndex J → Euclidean (n-1) → Euclidean n → ℝ}
    {m : RefinedIndex J × Euclidean (n-1) → ℝ}
    {L : RefinedIndex J → Euclidean (n-1) → Euclidean (n-1) → Euclidean n → Euclidean n}
    {K : Set (Euclidean n)} {DL DP EL EP : ℕ → ℝ} {rStar : ℕ} {T : ℝ}
    (h : OriginalSampledMomentGeometry.SampledChart φ Φ m L K DL DP rStar T)
    (hDL : ∀ j, DL j ≤ EL j) (hDP : ∀ j, DP j ≤ EP j) (hT : 1 ≤ T) :
    OriginalSampledMomentGeometry.SampledChart φ Φ m L K EL EP rStar T := by
  have hT0 := zero_le_one.trans hT
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,?_⟩
  intro r hr
  obtain ⟨hl,hp⟩ := h.2.2.2.2.2.2.2 r hr
  constructor
  · intro i η hm v hv x hx j
    exact (hl i η hm v hv x hx j).trans (mul_le_mul_of_nonneg_right (hDL j) (pow_nonneg hT0 _))
  · intro i η hm x hx j hj
    exact (hp i η hm x hx j hj).trans (mul_le_mul_of_nonneg_right (hDP j) (pow_nonneg hT0 _))

/-- The existing native hreserve pays the precise low/high kernel reserve;
there is no extra derivative or newly assumed source reserve. -/
theorem mean_kernel_reserve_le_native {n rStar : ℕ}
    (hreserve : 20 * (n+1) + 5 ≤ rStar) :
    2 * (n/2+2) + (n/2+1) + 5 ≤ rStar := by
  omega

private theorem mesh_nonneg {R : ℝ} (hR : 2 ≤ R) (j : ℕ) :
    0 ≤ historyScale R growthExponent j ^ (-separationExponent) := by
  have h : 1 ≤ R := by linarith
  exact Real.rpow_nonneg (zero_le_one.trans (h.trans (le_historyScale h j))) _

end JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate (bodyAt nodeAt)
private def root := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles
private def actual := root ++ `Actual
private def app (n : Name) (p : Array Expr) := mkAppN (mkConst n) p
private def part (e : Expr) (j : Nat) := Expr.proj ``And 0 (Nat.repeat (fun q => Expr.proj ``And 1 q) j e)
private def progress (s : String) : MetaM Unit := do
  let out ← IO.getStdout
  out.putStrLn s
  out.flush
private def save (key : Name) (xs : Array Expr) (proof : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType proof
  let type ← instantiateMVars (← mkForallFVars xs target)
  let value ← instantiateMVars (← mkLambdaFVars xs proof)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual quadratic realization {key}: missing {missing.toList}"
    if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasSorry then
      throwError "actual quadratic realization {key}: open proof"
  let shared := Lean.ShareCommon.shareCommon (type,value)
  let name := actual ++ key
  progress s!"kernel checking {name} / {xs.size}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := shared.1,value := shared.2,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := shared.1,value := shared.2}) (forceExpose := true)
  addDocStringCore name "Actual original primitive for the SAME fixed-source quadratic, without new source, sample, cutoff, or profile assumptions (app:ch_mean_pairs:eq:block-bilinear)."
  progress s!"kernel passed {name} / {xs.size}"

/-- Realize the whole four-μ cutoff plateau on its static original22 and row,
before any source, current history, frequency, or sampled shift. -/
elab "construct_actual_quadratic_cutoff_plateau" : command => liftTermElabM do
  let sb := `JanetCartan.PhysicalSeed.SelectedBoundary
  let source := `JanetCartan.PhysicalSampling.OriginalAdmission.cutoff_on_actual_selected_row
  forallBoundedTelescope (← getConstInfo source).type (some 23) fun p _ => do
    unless p.size == 23 do throwError "actual cutoff: changed static23"
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let i := p[22]!
    let merge := app `JanetCartan.PhysicalSampling.samplingCappedExtra #[p[0]!,p[1]!,p[2]!,p[21]!]
    let cap := app `JanetCartan.PhysicalNormalInverse.strongCappedExtra #[n,p[1]!,merge]
    let orig := (#[n,p[1]!] ++ p[3:22].toArray).set! 20 cap
    let μ := app (sb ++ `rMeasure) orig
    let b := app (sb ++ `a') (orig.push i)
    let inside := app ``OriginalMeanQuadraticProfiles.Actual.coreInCarrierSupport
      #[n,μ,b,app (sb ++ `hrMeasure) orig,app (sb ++ `ha') (orig.push i),app (sb ++ `fact60) (orig.push i)]
    let K := app (root ++ `Geometry.K) p[:22].toArray
    let plateau := part (app source p) 4
    let one ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 3)) 1
    let proof ← withLocalDeclNoLocalInstanceUpdate `x .default (app `JanetCartan.Euclidean #[n]) fun x => do
      withLocalDeclNoLocalInstanceUpdate `hx .default (← mkAppM ``Membership.mem #[K,x]) fun hx => do
        mkLambdaFVars #[x,hx] (mkAppN plateau #[one,x,mkAppN inside #[x,hx]])
    save `originalCutoff_plateau p proof

private def testerPayload (action : Expr) : MetaM (Expr × Array Expr) := do
  forallBoundedTelescope (← inferType action) (some 1) fun f r => do
    let some k := r.find? (·.isAppOfArity `JanetCartan.PhysicalMean.sampledMomentKernel 7)
      | throwError "actual tester: lost untouched original kernel"
    let a := k.getAppArgs[:5].toArray
    unless a.all (!·.hasLooseBVars) do throwError "actual tester: escaped physical variable"
    let t ← inferType f[0]!
    let some μ := t.find? (fun e => e.isAppOf `JanetCartan.PhysicalSamplingShells.sampledShellMeasure ||
      e.isAppOf `JanetCartan.PhysicalSamplingShells.annularShellMeasure)
      | throwError "actual tester: lost original input measure"
    return (μ,a)

/-- Use exactly the named common event, then restrict its input to the fixed
prefix. This does not choose another shift or change the native L² measure. -/
elab "construct_actual_quadratic_testers " which:num : command => liftTermElabM do
  let ev := `JanetCartan.PhysicalMean.OriginalCanonicalSelection.event
  forallBoundedTelescope (← getConstInfo ev).type (some 50) fun p _ => do
    let event := app ev p
    let full := part event 1
    let rows := part event 2
    withLocalDeclNoLocalInstanceUpdate `L .default (mkConst ``Nat) fun cut => do
      if which.getNat == 0 then
        forallBoundedTelescope (← inferType rows) (some 2) fun iq _ => do
          let h := mkAppN rows iq
          let e ← whnf (← inferType h)
          unless e.isAppOfArity ``Exists 2 do throwError "actual tester: lost original row tester"
          let (μ,a,cap) ← withLocalDeclNoLocalInstanceUpdate `T .default e.getAppArgs[0]! fun T => do
            withLocalDeclNoLocalInstanceUpdate `spec .default (e.getAppArgs[1]!.beta #[T]) fun hs => do
              let hnorm ← inferType (part hs 0)
              let (μ,a) ← testerPayload (.proj ``And 1 hs)
              return (μ,a,hnorm.getAppArgs[3]!)
          let J := a[1]!.getAppArgs[0]!.appArg!
          save `individualTester (p ++ #[cut] ++ iq) (app (actual ++ `gate_individual)
            #[a[0]!,J,cut,μ,a[2]!,a[3]!,a[4]!,cap,h])
      else
        let hn ← inferType (part full 0)
        let (μ,a) ← testerPayload (.proj ``And 1 full)
        let some w := a[3]!.find? (·.isAppOfArity `JanetCartan.PhysicalMean.originalWeightedHalfMask 5)
          | throwError "actual tester: lost original weighted half mask"
        let wa := w.getAppArgs
        let inst ← synthInstance (← mkAppM ``MeasurableSpace #[wa[1]!])
        let h := mkAppN (mkConst (actual ++ `gate_aggregate) [.zero])
          #[a[0]!,wa[2]!.appArg!,wa[1]!,inst,cut,μ,a[2]!,wa[3]!,wa[4]!,a[4]!,
            hn.getAppArgs[2]!.appArg!,hn.getAppArgs[3]!,full]
        save `aggregateTester (p.push cut) h

/-- Extract the actual common measurement jet bound from the original physical
profile. The row is eliminated, not selected; its cost remains native44. -/
elab "construct_actual_quadratic_measurement_jets" : command => liftTermElabM do
  let g := root ++ `Geometry
  let m := `JanetCartan.PhysicalMean.OriginalBackgroundMeasurementProfiles
  let bg := `JanetCartan.PhysicalMean.OriginalBackgroundHermitian
  let source := bg ++ `commonC_smooth
  forallBoundedTelescope (← getConstInfo source).type (some 50) fun p _ => do
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let outer ← bodyAt source p
    unless outer.isAppOfArity ``Nonempty.elim 4 do throwError "actual C: changed original row nonempty proof"
    let oa := outer.getAppArgs
    let fixed := p[:44].toArray
    let sampler ← JanetCartan.PhysicalSampling.OriginalBareScaleApplication.originalSampler p[:24].toArray
    unless sampler.size == 22 do throwError "actual C: changed static22"
    let K := app (g ++ `K) sampler
    let hK := app (g ++ `K_compact) sampler
    let hR ← mkAppM `le_trans #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed,p[45]!]
    let hT := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le
      #[p[44]!,hR,p[46]!]
    let common := app (bg ++ `commonC) p
    let CM := app (m ++ `CM) fixed
    let T := app `JanetCartan.currentCoefficientScale #[p[44]!,p[46]!]
    let (goal,all) ← withLocalDeclNoLocalInstanceUpdate `i .default oa[0]! fun i => do
      let profile := mkApp (app (m ++ `physical_profile) (p.push i)) K
      let pt ← inferType profile
      unless pt.isAppOfArity `JanetCartan.HasDerivativeProfile 11 do throwError "actual C: lost physical profile"
      let q := pt.getAppArgs
      let body := app ``OriginalMeanQuadraticProfiles.Actual.physical_measurement_jets
        #[n,q[1]!,q[4]!,q[5]!,K,common,CM,T,hK,app source p,app (m ++ `CM_nonneg) fixed,hT,profile]
      return (← inferType body,← mkLambdaFVars #[i] body)
    save `common_measurement_physical_jets p (mkAppN outer.getAppFn #[oa[0]!,goal,oa[2]!,all])

/-- Apply the original admitted window and OUTER patch bounds to the literal
sample weights. The zero-weight labels are retained. -/
elab "construct_actual_quadratic_weights_nonnegative" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalMean.OriginalCanonicalRow.weights
  forallBoundedTelescope (← getConstInfo source).type (some 51) fun p _ => do
    let raw ← bodyAt source p
    unless raw.isAppOfArity `JanetCartan.CanonicalRowComparison.sampleWeight 7 do
      throwError "actual weights: changed original sampleWeight7"
    let a := raw.getAppArgs
    let patch := a[3]!
    unless patch.isAppOfArity `JanetCartan.PhysicalSampling.OriginalOuterWeights.ψ 22 do
      throwError "actual weights: lost outer original22 patch"
    let D ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalRow.D p[:50].toArray
    unless D.isAppOfArity `JanetCartan.PhysicalSampling.OriginalJointEvent.measured_kernel 60 do
      throwError "actual weights: lost original window admission"
    let hw ← mkAppM `JanetCartan.PhysicalSampling.OriginalWindow.window_bounds #[D.getAppArgs[45]!]
    let hp := app `JanetCartan.PhysicalSampling.OriginalOuterWeights.patchBounds patch.getAppArgs
    let hR ← mkAppM `le_trans #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS p[:44].toArray,p[45]!]
    let hh := app ``OriginalMeanQuadraticProfiles.Actual.mesh_nonneg #[p[44]!,hR,p[46]!]
    save `sample_weights_nonneg p
      (← mkAppM `JanetCartan.CanonicalRowComparison.sampleWeight_nonneg #[a[6]!,hw,hp,hh])

/-- The aggregate cap is the SAME original square-root constant on native44,
not a bound extracted from a later sampled operator. -/
elab "construct_actual_quadratic_tester_cost" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.Ctest
  forallBoundedTelescope (← getConstInfo source).type (some 44) fun p _ => do
    let raw ← bodyAt source p
    unless raw.isAppOfArity `JanetCartan.PhysicalSampling.OriginalBareEvent.Ctest 46 do
      throwError "actual tester cost: changed original bare46 constant"
    let full ← bodyAt raw.getAppFn.constName! raw.getAppArgs
    unless full.isAppOfArity ``Real.sqrt 1 do throwError "actual tester cost: lost original square-root cap"
    let proof ← mkAppM ``Real.sqrt_nonneg #[full.appArg!]
    let target ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,app source p]
    save `testBudget_nonneg p proof false (some target)

/-- Replace the point's costs only by their fixed original patch totals. -/
elab "construct_actual_quadratic_chart_envelope" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (actual ++ `moment_chart)).type (some 56) fun p _ => do
    let h := app (actual ++ `moment_chart) p
    let a := (← inferType h).getAppArgs
    unless a.size == 11 do throwError "actual chart envelope: lost prefixed chart"
    let fixed := p[:44].toArray
    let row := fixed.push p[50]!
    let EL := app (actual ++ `directionBudgetTotal) fixed
    let EP := app (actual ++ `phaseBudgetTotal) fixed
    let hR ← mkAppM `le_trans #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed,p[45]!]
    let hT := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le
      #[p[44]!,hR,p[46]!]
    let term := app ``OriginalMeanQuadraticProfiles.Actual.chart_budget_mono
      (a[:9].toArray ++ #[EL,EP] ++ a[9:].toArray ++
        #[h,app (actual ++ `directionBudgetTotal.dominates) row,app (actual ++ `phaseBudgetTotal.dominates) row,hT])
    save `moment_chart_envelope p term

/-- Retain all-order regularity of the SAME global Q0, not the separately
published regularity of a raw adjoint input. -/
elab "construct_actual_quadratic_inverse_regularity" : command => liftTermElabM do
  OriginalCanonicalSourceApplication.withActualQuadratic fun p _ global _ _ => do
    save `Q0_regular p[:50].toArray
      (app `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.Q0_regular global)

private def getField (fields : Array (Name × Expr)) (key : Name) : MetaM Expr := do
  let hits := fields.filter (·.1 == key)
  unless hits.size == 1 do throwError "actual low quadratic: missing or repeated field {key}"
  return hits[0]!.2

private def binderKey (name : Name) (domain : Expr) (bi : BinderInfo) : Name := Id.run do
  if bi == .instImplicit then
    for (head,key) in #[( ``Fintype, `instFintype), (``MetricSpace, `instMetricSpace),
        (``DiscreteTopology, `instDiscreteTopology), (``MeasurableSpace, `instMeasurableSpace),
        (``BorelSpace, `instBorelSpace)] do
      if domain.isAppOf head then return key
  return name.eraseMacroScopes

/-- Apply ONLY the actual dictionary. No analytic input or replacement native
instance can silently be synthesized by a downstream consumer. -/
private def applyFields (name : Name) (fields : Array (Name × Expr)) : MetaM Expr := do
  let info ← getConstInfo name
  let levels := info.levelParams.map (fun _ => Level.zero)
  let mut term := mkConst name levels
  let mut type := info.type.instantiateLevelParams info.levelParams levels
  while type.isForall do
    let .forallE binder domain body bi := type | throwError "actual low quadratic: changed binder"
    let value ← getField fields (binderKey binder domain bi)
    term := mkApp term value
    type := body.instantiate1 value
  return term

private def inverseFields (params : Array Expr) (fields : Array (Name × Expr)) : MetaM (Array (Name × Expr)) := do
  unless params.size == 53 do throwError "actual low quadratic: expected native50+numerical guards+fixed L"
  let ns := `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles
  let Cinv := app (ns ++ `Cinv) params[:44].toArray
  let hCinv := app (ns ++ `Cinv_nonneg) params[:44].toArray
  for (key,value) in #[(`Cinv,Cinv),(`hCinv,hCinv)] do
    for old in fields.filter (·.1 == key) do
      unless ← isDefEq old.2 value do throwError "actual low quadratic: changed same global {key}"
  return (fields.filter (fun e => e.1 != `Cinv && e.1 != `hCinv)) ++ #[(`Cinv,Cinv),(`hCinv,hCinv)]

private def lowCostPrefix (params : Array Expr) (fields : Array (Name × Expr)) : MetaM (Array Expr) := do
  for key in #[`n,`N,`Rbox,`χ,`hχ,`hχs,`hχcell,`aC,`aG,`p,`Badj,`Cinv,
      `haC,`haG,`hp,`hBadj,`hCinv,`Cbare,`Ctest,`hCtest] do
    let value ← getField fields key
    for x in params[44:].toArray do
      if value.containsFVar x.fvarId! then
        throwError "actual low quadratic: late history/guard/prefix in static cost {key}"
  return params[:44].toArray

/-- Freeze the actual low Picard constant before R0, current history, the ONE
sampled shift, prefix and both source arguments. -/
def publishLowBudget (params : Array Expr) (original : Array (Name × Expr)) : MetaM Unit := do
  let fields ← inverseFields params original
  let fixed ← lowCostPrefix params fields
  let cost ← applyFields `JanetCartan.PhysicalMean.canonicalLowQuadraticConstant fields
  save `lowConstant fixed cost true
  let proof ← applyFields `JanetCartan.PhysicalMean.canonicalLowQuadraticConstant_nonneg fields
  let target := (← inferType proof).replace fun e => if e == cost then some (app (actual ++ `lowConstant) fixed) else none
  save `lowConstant_nonneg fixed proof false (some target)

/-- Instantiate the original global Q0 regularity or inverse profile. Only the
legitimate low source-order inequality is bound; no source estimate is assumed. -/
private def lowSourceTail (params : Array Expr) (fields : Array (Name × Expr))
    (key : Name) (domain : Expr) : MetaM Expr := do
  let n ← getField fields `n
  let u ← getField fields (if key == `hregu || key == `hinverseu then `u else `v)
  let w ← mkAppM ``DFunLike.coe #[mkApp (mkConst `JanetCartan.CurrentMean.smoothResidualToL2) n,u]
  let regular := key == `hregu || key == `hregv
  forallBoundedTelescope domain (some (if regular then 1 else 2)) fun args _ => do
    let j := args[0]!
    let hw := app `JanetCartan.CurrentMean.smoothResidualToL2_mem #[n,u,j]
    let producer ← if regular then getField fields `Q0_regular else
      pure (app `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles.inverse_profile params[:50].toArray)
    mkLambdaFVars args (mkAppN producer #[j,w,hw])

/-- The asymmetric endpoint is exactly H^0(u) H^(n/2+2)(v), applied to14's
unchanged quadratic at the ONE selected shift and fixed prefix. Only u and v
are newly quantified; every analytic primitive is required from the actual tuple. -/
partial def publishLowBound (params : Array Expr) (original : Array (Name × Expr)) : MetaM Unit := do
  let common ← inverseFields params original
  let fixed ← lowCostPrefix params common
  let consumer := `JanetCartan.PhysicalMean.fixedSourceQuadratic_low_bound
  let info ← getConstInfo consumer
  let levels := info.levelParams.map (fun _ => Level.zero)
  let literal := mkConst consumer levels
  let rec go (type : Expr) (args : Array Expr) (fields : Array (Name × Expr))
      (sources : Array Expr) : MetaM Unit := do
    match type with
    | .forallE binder domain body bi =>
      let key := binderKey binder domain bi
      if #[`hregu,`hregv,`hinverseu,`hinversev].contains key then
        let proof ← lowSourceTail params fields key domain
        go (body.instantiate1 proof) (args.push proof) (fields.push (key,proof)) sources
      else if key == `u || key == `v then
        unless (fields.filter (·.1 == key)).isEmpty do throwError "actual low quadratic: source leaked into static tuple"
        withLocalDeclNoLocalInstanceUpdate binder bi domain fun x =>
          go (body.instantiate1 x) (args.push x) (fields.push (key,x)) (sources.push x)
      else
        let value ← getField fields key
        go (body.instantiate1 value) (args.push value) fields sources
    | target =>
      unless sources.size == 2 do throwError "actual low quadratic: changed asymmetric source arguments"
      let rawCost ← applyFields `JanetCartan.PhysicalMean.canonicalLowQuadraticConstant fields
      let cost := app (actual ++ `lowConstant) fixed
      let p := params[:50].toArray
      let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift p
      let quadratic := app `JanetCartan.PhysicalMean.OriginalCanonicalSource.quadratic (p ++ #[shift,params[52]!])
      let some rawQuadratic := target.find? (·.isAppOf `JanetCartan.PhysicalMean.fixedSourceQuadratic)
        | throwError "actual low quadratic: lost exact fixed source operator"
      let target := target.replace fun e =>
        if e == rawCost then some cost else if e == rawQuadratic then some quadratic else none
      unless (target.find? (·.isAppOf (actual ++ `lowConstant))).isSome &&
          (target.find? (·.isAppOf `JanetCartan.PhysicalMean.OriginalCanonicalSource.quadratic)).isSome do
        throwError "actual low quadratic: named original estimate target missing"
      save `low_bound params (← mkLambdaFVars sources (mkAppN literal args)) false
        (some (← mkForallFVars sources target))
  go (info.type.instantiateLevelParams info.levelParams levels) #[] common #[]

end JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization
end

construct_actual_quadratic_cutoff_plateau
construct_actual_quadratic_measurement_jets
construct_actual_quadratic_weights_nonnegative
construct_actual_quadratic_inverse_regularity
construct_actual_quadratic_tester_cost
construct_actual_quadratic_chart_envelope
construct_actual_quadratic_testers 0
construct_actual_quadratic_testers 1
