module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.FiniteSlices
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.SpatialBudget

/-!
# The original fixed-time graph from finite multiplier budgets

Absolute frequency convergence and Fubini identify the actual elapsed graph
with the original spatial graph of the function-valued multiplier slice.
Consumer: the parent's same fixed-time strong limit in
`app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
open FourierIntegral KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

/-- Supported primitive continuity and the original symbol bound imply
absolute frequency integrability without a compact frequency cutoff.
The bound `hbound` is supplied by `norm_elapsedSpatialAmplitude_le_orderSeminorm`;
it is a pointwise symbol bound, not an operator estimate. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integrable_uncutFixedTimeFourierIntegrand_of_bound
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (β : E → ℂ)
    (v : SchwartzMap E V) (t s : ℝ) (y : Euclidean d)
    (hΨ : ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ Ψ t s y (spatialPart ξ)) ξ)
    (hb : ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ b t s y (spatialPart ξ)) ξ)
    (hβ : Continuous β) (Cβ : ℝ) (hβbound : ∀ ξ, ‖β ξ‖ ≤ Cβ) (C : ℝ)
    (hbound : ∀ ξ ∈ tsupport β, ‖b t s y (spatialPart ξ)‖ ≤ C) :
    Integrable (cutFixedTimeFourierIntegrand Ψ b β (fun _ ↦ 1) v t s y) := by
  let f : E → V := fun ξ ↦ β ξ • sourceInputFourierTransform v ξ
  have hf (ξ : E) : f ξ = β ξ • sourceInputFourierTransform v ξ := rfl
  have hfc : Continuous f := hβ.smul (sourceInputFourierTransform v).continuous
  have hfi : Integrable f := integrable_multiplierFrequencyData β hβ v Cβ hβbound
  have hsupport : tsupport (cutFixedTimeFourierIntegrand Ψ b β (fun _ ↦ 1) v t s y)
      ⊆ tsupport β := by
    apply closure_minimal _ (isClosed_tsupport β)
    intro ξ hξ
    by_contra hn
    exact hξ (by simp [cutFixedTimeFourierIntegrand, image_eq_zero_of_notMem_tsupport hn])
  have hc : Continuous (cutFixedTimeFourierIntegrand Ψ b β (fun _ ↦ 1) v t s y) := by
    apply continuous_of_tsupport
    intro ξ hξ
    have hmem := hsupport hξ
    have hmv : ContinuousAt (fun ξ : E ↦ (b t s y (spatialPart ξ)).mulVec (f ξ)) ξ := by
      exact (show Continuous (fun p : Matrix (Fin q) (Fin q) ℂ × V ↦ p.1.mulVec p.2)
        from continuous_fst.matrix_mulVec continuous_snd).continuousAt.comp
          ((hb ξ hmem).prodMk hfc.continuousAt)
    unfold cutFixedTimeFourierIntegrand
    simpa only [one_mul, hf, Pi.smul_def', Pi.mul_def, Function.comp_def] using
      (show ContinuousAt (fun ξ : E ↦ Complex.exp (Complex.I * ((s * ξ 0 : ℝ) : ℂ))) ξ
        by fun_prop).smul
        (((continuousAt_const (y := Complex.I)).mul (Complex.continuous_ofReal.continuousAt.comp
          (hΨ ξ hmem))).cexp.smul hmv)
  apply (hfi.norm.const_mul ((sourceMatrixAction (r := q)).opNorm * C)).mono'
    hc.aestronglyMeasurable
  filter_upwards [] with ξ
  by_cases hξ : ξ ∈ tsupport β
  · simp only [cutFixedTimeFourierIntegrand, one_mul, ← hf, norm_smul,
      mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul]
    calc
      _ ≤ (sourceMatrixAction (r := q)).opNorm * ‖b t s y (spatialPart ξ)‖ * ‖f ξ‖ :=
        (sourceMatrixAction (r := q)).le_opNorm₂ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbound ξ hξ) (sourceMatrixAction (r := q)).opNorm_nonneg)
          (norm_nonneg _)
  · simp [cutFixedTimeFourierIntegrand, hf, image_eq_zero_of_notMem_tsupport hξ]

/-- Genuine Fubini for the uncut fixed-time kernel. All temporal-fiber
integrability is proved from the original multiplier symbol, and the full
integrability is supplied by the primitive spatial symbol bound. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integral_uncutFixedTimeFourier_of_bound
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (β : E → ℂ)
    (hβ : Continuous β) (v : SchwartzMap E V)
    (Cβ : ℝ) (hβbound : ∀ ξ, ‖β ξ‖ ≤ Cβ)
    (t s : ℝ) (y : Euclidean d)
    (hΨ : ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ Ψ t s y (spatialPart ξ)) ξ)
    (hb : ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ b t s y (spatialPart ξ)) ξ)
    (C : ℝ) (hbound : ∀ ξ ∈ tsupport β, ‖b t s y (spatialPart ξ)‖ ≤ C) :
    ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ •
      (∫ ξ, cutFixedTimeFourierIntegrand Ψ b β (fun _ ↦ 1) v t s y ξ) =
      cutFixedTimeFourier Ψ b β (fun _ ↦ 1) v t s y := by
  rw [integral_eq_space_time _
    (integrable_uncutFixedTimeFourierIntegrand_of_bound Ψ b β v t s y hΨ hb hβ Cβ hβbound C hbound)]
  have he (η : Euclidean d) :
      (∫ τ, cutFixedTimeFourierIntegrand Ψ b β (fun _ ↦ 1) v t s y (timeSpacePoint τ η)) =
      Complex.exp (Complex.I * (Ψ t s y η : ℂ)) •
        (b t s y η).mulVec (∫ τ, cutTemporalFourierIntegrand β (fun _ ↦ 1) v s η τ) := by
    have hi := integrable_uncutTemporalFourierIntegrand_of_bound β hβ v Cβ hβbound s η
    have hL := (sourceMatrixAction (b t s y η)).integral_comp_comm hi
    change (∫ τ, (b t s y η).mulVec (cutTemporalFourierIntegrand β (fun _ ↦ 1) v s η τ)) =
      (b t s y η).mulVec (∫ τ, cutTemporalFourierIntegrand β (fun _ ↦ 1) v s η τ) at hL
    rw [← hL, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with τ
    simp only [cutFixedTimeFourierIntegrand, timeSpacePoint_time, spatialPart_timeSpacePoint,
      cutTemporalFourierIntegrand, Matrix.mulVec_smul]
    exact smul_comm _ _ _
  simp_rw [he]
  unfold cutFixedTimeFourier cutTemporalFourierSlice
  simp only [Matrix.mulVec_smul]
  simp_rw [smul_comm _ ((2 * Real.pi : ℂ)⁻¹), integral_smul, smul_smul]
  congr 1
  rw [pow_succ, mul_inv_rev]
  exact mul_comm _ _

/-- The literal uncut fixed-`r` graph on the original test space is
`Mχout U_b Bβ Mχsource`. Both masks, the original multiplier, and the two
original time arguments are unchanged. Consumer: identification of the
strong fixed-time limit exported by `PrimitiveRetarded`, in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem uncut_elapsedGraph_eq_spatialGraph_of_finite_bounds
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (Cβ : ℕ → ℝ)
    (hβbound : ∀ k ≤ d + 2, ∀ ξ, ‖iteratedFDeriv ℝ k β ξ‖ ≤ Cβ k)
    (r : ℝ) (u : graphTestSpace (d + 1) q) (x : E)
    (hΨ : x ∈ tsupport χout → ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ Ψ (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)) ξ)
    (hb : x ∈ tsupport χout → ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)) ξ)
    (C : ℝ) (hbound : x ∈ tsupport χout → ∀ ξ ∈ tsupport β,
      ‖b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)‖ ≤ C) :
    graphOperator (elapsedPhase Ψ r) (elapsedAmplitude b χout χsource β r)
      (fun z ↦ (u.val z).ofLp) x =
      χout x • graphOperator (Ψ (x 0) (x 0 - r))
        (fun y _ η ↦ b (x 0) (x 0 - r) y η)
        (fun z ↦ physicalMultiplierIntegral β
          (LowBounds.FrequencyCutoff.graphTestToSchwartz
            (complexSourceMaskTest χsource hs u)) (timeSpacePoint (x 0 - r) z)) (spatialPart x) := by
  have he := cut_elapsedGraph_eq_sourceFourierIntegral Ψ b χout χsource β
    (fun _ ↦ 1) hs r u x
  unfold frequencyCutFullAmplitude at he
  simp only [one_smul] at he
  rw [he]
  by_cases hx : χout x = 0
  · simp [hx]
  rw [← uncutFixedTimeFourier_eq_graphOperator_of_finite_bounds Ψ b β hβ _ Cβ hβbound]
  apply congrArg (χout x • ·)
  exact integral_uncutFixedTimeFourier_of_bound Ψ b β hβ.continuous _ (Cβ 0)
    (fun ξ ↦ by simpa only [norm_iteratedFDeriv_zero] using hβbound 0 (by omega) ξ) _ _ _
    (hΨ (subset_tsupport χout hx)) (hb (subset_tsupport χout hx)) C
    (hbound (subset_tsupport χout hx))

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
