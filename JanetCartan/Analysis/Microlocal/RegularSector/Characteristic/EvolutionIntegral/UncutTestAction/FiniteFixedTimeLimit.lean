module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.FiniteFixedTime
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedFixedTime
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The same fixed-time strong limit under finite symbol bounds

Dominated convergence proves pointwise convergence to the original uncut test
action. The exact fixed-time strong-limit and cutoff-preservation conclusions
exported by `exists_retardedOperator_of_primitive_data` then identify its
bounded elapsed graph with that action. No convergence to the desired uncut
formula is an input. Source: `app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction

open FourierIntegral KernelIdentification LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ


/-- Dominated convergence removes the physical frequency cutoff from the
actual fixed-time spectral integral. Its integrable majorant is proved from
the original multiplier and spatial symbol bounds. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem tendsto_integral_uncutFixedTimeFourier_of_bound
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (β : E → ℂ)
    (hβ : ContDiff ℝ ∞ β) (v : SchwartzMap E V)
    (Cβ : ℝ) (hβbound : ∀ ξ, ‖β ξ‖ ≤ Cβ)
    (t s : ℝ) (y : Euclidean d)
    (hΨ : ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ Ψ t s y (spatialPart ξ)) ξ)
    (hb : ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ b t s y (spatialPart ξ)) ξ)
    (C : ℝ) (hbound : ∀ ξ ∈ tsupport β, ‖b t s y (spatialPart ξ)‖ ≤ C) :
    Tendsto (fun j ↦ ∫ ξ, cutFixedTimeFourierIntegrand Ψ b β
      (complexPhysicalCutoff j) v t s y ξ) atTop
      (𝓝 (∫ ξ, cutFixedTimeFourierIntegrand Ψ b β (fun _ ↦ 1) v t s y ξ)) := by
  let F := cutFixedTimeFourierIntegrand Ψ b β (fun _ ↦ 1) v t s y
  have hi : Integrable F :=
    integrable_uncutFixedTimeFourierIntegrand_of_bound Ψ b β v t s y hΨ hb
      hβ.continuous Cβ hβbound C hbound
  simp_rw [cutFixedTimeFourierIntegrand_eq_frequency_smul Ψ b β (complexPhysicalCutoff _) v t s y]
  apply tendsto_integral_of_dominated_convergence (fun ξ ↦ ‖F ξ‖)
  · intro j
    exact (complexPhysicalCutoff_contDiff j).continuous.aestronglyMeasurable.smul
      hi.aestronglyMeasurable
  · exact hi.norm
  · intro j
    filter_upwards [] with ξ
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (complexPhysicalCutoff_norm_le j ξ)
      (norm_nonneg _)).trans_eq (one_mul _)
  · filter_upwards [] with ξ
    simpa only [one_smul] using (complexPhysicalCutoff_tendsto ξ).smul_const (F ξ)

/-- Pointwise removal of the physical cutoff on the original masked graph
test action. Only supported phase continuity and primitive symbol bounds are
needed, with no assumed operator or uncut-kernel convergence. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem tendsto_uncut_elapsedGraph_test_of_bound
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (Cβ : ℝ) (hβbound : ∀ ξ, ‖β ξ‖ ≤ Cβ)
    (r : ℝ) (u : graphTestSpace (d + 1) q) (x : E)
    (hΨ : x ∈ tsupport χout → ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ Ψ (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)) ξ)
    (hb : x ∈ tsupport χout → ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)) ξ)
    (C : ℝ) (hbound : x ∈ tsupport χout → ∀ ξ ∈ tsupport β,
      ‖b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)‖ ≤ C) :
    Tendsto (fun j ↦ graphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude (complexPhysicalCutoff j) (elapsedAmplitude b χout χsource β r))
      (fun z ↦ (u.val z).ofLp) x) atTop
      (𝓝 (graphOperator (elapsedPhase Ψ r) (elapsedAmplitude b χout χsource β r)
        (fun z ↦ (u.val z).ofLp) x)) := by
  have he := cut_elapsedGraph_eq_sourceFourierIntegral Ψ b χout χsource β
    (fun _ ↦ 1) hs r u x
  unfold frequencyCutFullAmplitude at he
  simp only [one_smul] at he
  simp_rw [cut_elapsedGraph_eq_sourceFourierIntegral Ψ b χout χsource β _ hs r u x]
  rw [he]
  by_cases hx : χout x = 0
  · simp only [hx, zero_smul]
    exact tendsto_const_nhds
  exact ((tendsto_integral_uncutFixedTimeFourier_of_bound Ψ b β hβ _ Cβ hβbound _ _ _
    (hΨ (subset_tsupport χout hx)) (hb (subset_tsupport χout hx)) C
    (hbound (subset_tsupport χout hx))).const_smul
      (((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹)).const_smul (χout x)

/-- The exact fixed-time strong limit exported by
`exists_retardedOperator_of_primitive_data` is the ORIGINAL uncut physical
test action. `hcut` and `hstrong` have precisely that producer's signatures;
the proof supplies the pointwise uncut limit by dominated convergence and uses
an almost-everywhere convergent subsequence of the strong limit. All masks and
the source time `x₀-r` remain in their original order. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem elapsedGraph_eq_uncutSpatialGraph_of_finite_bounds_strongLimit
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (Cβ : ℕ → ℝ)
    (hβbound : ∀ k ≤ d + 2, ∀ ξ, ‖iteratedFDeriv ℝ k β ξ‖ ≤ Cβ k)
    (χ : ℕ → E → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hχcs : ∀ j, HasCompactSupport (χ j))
    (hcut : ∀ A : FullAmplitude (d + 1) q,
      (∀ x y ξ, ξ ∉ tsupport β → A x y ξ = 0) → ∀ j,
      frequencyCutFullAmplitude (χ j) A = frequencyCutFullAmplitude (complexPhysicalCutoff j) A)
    (r : ℝ) (u : graphTestSpace (d + 1) q)
    (hΨ : ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ Ψ (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)) ξ)
    (hb : ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)) ξ)
    (C : ℝ) (hbound : ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ‖b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)‖ ≤ C)
    (hstrong : ∃ R : ℕ → SpacetimeL2 d q,
      (∀ j, R j =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (χout x • graphOperator (Ψ (x 0) (x 0 - r))
          (fun y _ η ↦ b (x 0) (x 0 - r) y η)
          (cutPhysicalMultiplierSlice β (χ j)
            (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
            hβ (hχ j) (hχcs j) (x 0 - r)) (spatialPart x))) ∧
      Tendsto R atTop (𝓝 (elapsedGraph Ψ b χout χsource β r (graphTestToLp u)))) :
    elapsedGraph Ψ b χout χsource β r (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (χout x • graphOperator (Ψ (x 0) (x 0 - r))
        (fun y _ η ↦ b (x 0) (x 0 - r) y η)
        (fun z ↦ physicalMultiplierIntegral β
          (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
          (timeSpacePoint (x 0 - r) z)) (spatialPart x)) := by
  obtain ⟨R, hR, hlim⟩ := hstrong
  have hecut := hcut (elapsedAmplitude b χout χsource β r)
    (fun x y ξ hξ ↦ elapsedAmplitude_eq_zero_of_mask b χout χsource β r x y ξ
      (Or.inr (Or.inr (image_eq_zero_of_notMem_tsupport hξ))))
  have hreal (j : ℕ) : R j =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude (complexPhysicalCutoff j) (elapsedAmplitude b χout χsource β r)) u := by
    apply (hR j).trans
    apply Eventually.of_forall
    intro x
    apply congrArg (WithLp.toLp 2)
    rw [← hecut j]
    exact (cut_elapsedGraph_eq_spatialGraph_of_support Ψ b χout χsource β (χ j)
      hs r u x (hΨ x) (hb x) hβ (hχ j) (hχcs j)).symm
  obtain ⟨s, hs', hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  filter_upwards [hsub, ae_all_iff.mpr hreal] with x hx he
  have ht := (PiLp.continuous_toLp 2 (fun _ : Fin q ↦ ℂ)).tendsto _ |>.comp
    (tendsto_uncut_elapsedGraph_test_of_bound Ψ b χout χsource β hs hβ (Cβ 0)
      (fun ξ ↦ by simpa only [norm_iteratedFDeriv_zero] using hβbound 0 (by omega) ξ) r u x
      (hΨ x) (hb x) C (hbound x))
  have hx' := tendsto_nhds_unique hx
    ((ht.comp hs'.tendsto_atTop).congr (fun j ↦ (he (s j)).symm))
  exact hx'.trans (congrArg (WithLp.toLp 2)
    (uncut_elapsedGraph_eq_spatialGraph_of_finite_bounds Ψ b χout χsource β hs hβ
      Cβ hβbound r u x
      (hΨ x) (hb x) C (hbound x)))

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
