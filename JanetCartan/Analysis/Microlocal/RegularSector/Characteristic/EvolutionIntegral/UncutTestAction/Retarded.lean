module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.RetardedBounds

/-!
# Removing the frequency cutoff in the original retarded test action

The primitive symbol majorant and continuity of the compact regularizations
prove time integrability and dominated convergence for the uncut action.
The original lower buffer then converts the fixed elapsed slab to the literal
retarded interval, including its endpoints. Source:
`app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction

open FourierIntegral KernelIdentification LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

/-- Time integrability and cutoff removal follow from the primitive pointwise
symbol bound, independently of any integrated operator estimate. The supported
continuity hypotheses are precisely those proved by `PrimitiveRetarded` from
its original phase and amplitude. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integrable_and_tendsto_integral_uncut_elapsedGraph
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hs : ContDiff ℝ ∞ χsource) (hβ : β.HasTemperateGrowth)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ‖b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)‖ ≤ C)
    (u : graphTestSpace (d + 1) q) (x : E) :
    IntegrableOn (fun r ↦ graphOperator (elapsedPhase Ψ r)
      (elapsedAmplitude b χout χsource β r) (fun z ↦ (u.val z).ofLp) x) (Icc 0 Δ) ∧
    Tendsto (fun j ↦ ∫ r in Icc 0 Δ, graphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude (complexPhysicalCutoff j) (elapsedAmplitude b χout χsource β r))
      (fun z ↦ (u.val z).ofLp) x) atTop
      (𝓝 (∫ r in Icc 0 Δ, graphOperator (elapsedPhase Ψ r)
        (elapsedAmplitude b χout χsource β r) (fun z ↦ (u.val z).ofLp) x)) := by
  let G := fun (θ : E → ℂ) r ↦ graphOperator (elapsedPhase Ψ r)
    (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r))
    (fun z ↦ (u.val z).ofLp) x
  let g := fun r ↦ graphOperator (elapsedPhase Ψ r)
    (elapsedAmplitude b χout χsource β r) (fun z ↦ (u.val z).ofLp) x
  let B := ‖χout x‖ * ‖((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹‖ *
    ((sourceMatrixAction (r := q)).opNorm * C *
      ∫ ξ, ‖SchwartzMap.smulLeftCLM V β (sourceInputFourierTransform
        (graphTestToSchwartz (complexSourceMaskTest χsource hs u))) ξ‖)
  have hm (j : ℕ) : AEStronglyMeasurable (G (complexPhysicalCutoff j))
      (volume.restrict (Icc 0 Δ)) := by
    have hc := (continuous_supported_elapsed_cut_outputs Ψ b χout χsource β Δ hΔ
      hΨ hb ho hs.continuous hβ.1.continuous hocs hscs (complexPhysicalCutoff j)
      (complexPhysicalCutoff_contDiff j).continuous (complexPhysicalCutoff_hasCompactSupport j) u).1
    have hc' := (PiLp.continuous_ofLp 2 (fun _ : Fin q ↦ ℂ)).comp
      (hc.comp (continuous_id.prodMk (continuous_const (y := x))))
    apply hc'.aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    simp only [Function.comp_def, graphTestOutput, id_eq,
      min_eq_right hr.2, max_eq_right hr.1, G]
  have hlim : ∀ᵐ r ∂volume.restrict (Icc 0 Δ),
      Tendsto (fun j ↦ G (complexPhysicalCutoff j) r) atTop (𝓝 (g r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    apply tendsto_uncut_elapsedGraph_test Ψ b χout χsource β hs hβ r u x
      _ _ C (hbound r hr x)
    · intro hx ξ hξ
      exact (hΨ r hr x hx ξ hξ).comp (f := fun ξ : E ↦
        ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
        (continuous_const.prodMk (continuous_const.prodMk continuous_spatialPart)).continuousAt
    · intro hx ξ hξ
      exact (hb r hr x hx ξ hξ).comp (f := fun ξ : E ↦
        ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
        (continuous_const.prodMk (continuous_const.prodMk continuous_spatialPart)).continuousAt
  have hB (j : ℕ) : ∀ᵐ r ∂volume.restrict (Icc 0 Δ), ‖G (complexPhysicalCutoff j) r‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact norm_cut_elapsedGraph_le_symbol_majorant Ψ b χout χsource β _ hs hβ
      (complexPhysicalCutoff_norm_le j) r u x C hC (hbound r hr x)
  have hg : AEStronglyMeasurable g (volume.restrict (Icc 0 Δ)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hm hlim
  refine ⟨(integrable_const B).mono' hg ?_, ?_⟩
  · filter_upwards [hlim, ae_all_iff.mpr hB] with r hr hBr
    exact le_of_tendsto hr.norm (Eventually.of_forall hBr)
  · exact tendsto_integral_of_dominated_convergence (fun _ ↦ B) hm (integrable_const B) hB hlim

/-- The uncut elapsed slab is exactly the original physical retarded test
formula. Time integrability was proved from symbols, and the original lower
buffer removes the excess slab without changing the endpoints. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integral_uncut_elapsedGraph_eq_retardedPhysical
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hs : ContDiff ℝ ∞ χsource) (hβ : β.HasTemperateGrowth)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ‖b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)‖ ≤ C)
    (a : ℝ) (hout : ∀ x, χout x ≠ 0 → x 0 ∈ Icc a (a + Δ))
    (hzero : ∀ t s y η, s ≤ a → b t s y η = 0)
    (u : graphTestSpace (d + 1) q) (x : E) :
    (∫ r in Icc 0 Δ, graphOperator (elapsedPhase Ψ r)
      (elapsedAmplitude b χout χsource β r) (fun z ↦ (u.val z).ofLp) x) =
      retardedPhysical Ψ b χout χsource β hs a u x := by
  by_cases hx : χout x = 0
  · simp [graphOperator, elapsedAmplitude, hx, retardedPhysical]
  let f : ℝ → V := fun s ↦ χout x • graphOperator (Ψ (x 0) s)
    (fun y _ η ↦ b (x 0) s y η)
    (physicalMultiplierSlice β (graphTestToSchwartz (complexSourceMaskTest χsource hs u)) s)
    (spatialPart x)
  have he (r : ℝ) (hr : r ∈ Icc 0 Δ) :
      graphOperator (elapsedPhase Ψ r) (elapsedAmplitude b χout χsource β r)
        (fun z ↦ (u.val z).ofLp) x = f (x 0 - r) := by
    apply uncut_elapsedGraph_eq_spatialGraph Ψ b χout χsource β hs hβ r u x
      _ _ C (hbound r hr x)
    · intro hx ξ hξ
      exact (hΨ r hr x hx ξ hξ).comp (f := fun ξ : E ↦
        ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
        (continuous_const.prodMk (continuous_const.prodMk continuous_spatialPart)).continuousAt
    · intro hx ξ hξ
      exact (hb r hr x hx ξ hξ).comp (f := fun ξ : E ↦
        ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
        (continuous_const.prodMk (continuous_const.prodMk continuous_spatialPart)).continuousAt
  have hae : (fun r ↦ graphOperator (elapsedPhase Ψ r)
      (elapsedAmplitude b χout χsource β r) (fun z ↦ (u.val z).ofLp) x)
      =ᵐ[volume.restrict (Icc 0 Δ)] fun r ↦ f (x 0 - r) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact he r hr
  have hi : IntervalIntegrable (fun r ↦ f (x 0 - r)) volume 0 Δ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hΔ]
    exact (integrable_and_tendsto_integral_uncut_elapsedGraph Ψ b χout χsource β Δ hΔ
      hΨ hb ho hs hβ hocs hscs C hC hbound u x).1.congr hae
  calc
    _ = ∫ r in Icc 0 Δ, f (x 0 - r) := integral_congr_ae hae
    _ = ∫ s in a..x 0, f s := integral_fixed_slab_eq_retarded (hout x hx).1
      (by linarith [(hout x hx).2]) f hi (fun s hs ↦ by
        simp only [f, graphOperator, hzero _ _ _ _ hs, Matrix.zero_mulVec, smul_zero, integral_zero])
    _ = _ := intervalIntegral.integral_smul _ _

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
