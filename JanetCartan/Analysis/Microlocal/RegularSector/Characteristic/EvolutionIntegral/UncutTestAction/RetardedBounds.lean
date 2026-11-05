module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.FixedTimeLimit
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedRetarded

/-!
# A cutoff-independent pointwise majorant for the retarded test action

The original spatial symbol bound and the Schwartz multiplier datum give an
integrable frequency majorant, uniform in elapsed time. This is a pointwise
test-function bound, not an integrated Sobolev estimate. Its consumer is the
uncut passage in `app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction

open FourierIntegral KernelIdentification LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

/-- The primitive spatial symbol bound gives one pointwise majorant for all
physical frequency cutoffs and elapsed times. Consumer: retarded dominated
convergence in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem norm_cut_elapsedGraph_le_symbol_majorant
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β θ : E → ℂ)
    (hs : ContDiff ℝ ∞ χsource) (hβ : β.HasTemperateGrowth)
    (hθ : ∀ ξ, ‖θ ξ‖ ≤ 1) (r : ℝ) (u : graphTestSpace (d + 1) q) (x : E)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : x ∈ tsupport χout → ∀ ξ ∈ tsupport β,
      ‖b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)‖ ≤ C) :
    ‖graphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r))
      (fun z ↦ (u.val z).ofLp) x‖ ≤
      ‖χout x‖ * ‖((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹‖ *
        ((sourceMatrixAction (r := q)).opNorm * C *
          ∫ ξ, ‖SchwartzMap.smulLeftCLM V β
            (sourceInputFourierTransform
              (graphTestToSchwartz (complexSourceMaskTest χsource hs u))) ξ‖) := by
  rw [cut_elapsedGraph_eq_sourceFourierIntegral Ψ b χout χsource β θ hs r u x]
  by_cases hx : χout x = 0
  · simp [hx]
  let v := graphTestToSchwartz (complexSourceMaskTest χsource hs u)
  let f := SchwartzMap.smulLeftCLM V β (sourceInputFourierTransform v)
  have hf (ξ : E) : f ξ = β ξ • sourceInputFourierTransform v ξ :=
    SchwartzMap.smulLeftCLM_apply_apply hβ _ _
  have hi : ‖∫ ξ, cutFixedTimeFourierIntegrand Ψ b β θ v
      (x 0) (x 0 - r) (spatialPart x) ξ‖ ≤
      (sourceMatrixAction (r := q)).opNorm * C * ∫ ξ, ‖f ξ‖ := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (f.integrable.norm.const_mul _)
    filter_upwards [] with ξ
    by_cases hξ : ξ ∈ tsupport β
    · have hfactor : (θ ξ * β ξ) • sourceInputFourierTransform v ξ = θ ξ • f ξ := by
        rw [hf, mul_smul]
      simp only [cutFixedTimeFourierIntegrand, hfactor, Matrix.mulVec_smul,
        norm_smul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul]
      calc
        _ ≤ ‖(b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)).mulVec (f ξ)‖ :=
          (mul_le_mul_of_nonneg_right (hθ ξ) (norm_nonneg _)).trans_eq (one_mul _)
        _ ≤ (sourceMatrixAction (r := q)).opNorm *
            ‖b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)‖ * ‖f ξ‖ :=
          (sourceMatrixAction (r := q)).le_opNorm₂ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hbound (subset_tsupport χout hx) ξ hξ)
            (sourceMatrixAction (r := q)).opNorm_nonneg) (norm_nonneg _)
    · simp only [cutFixedTimeFourierIntegrand, image_eq_zero_of_notMem_tsupport hξ,
        mul_zero, zero_smul, Matrix.mulVec_zero, smul_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (sourceMatrixAction (r := q)).opNorm_nonneg hC)
        (norm_nonneg _)
  simpa only [norm_smul, mul_assoc, cutFixedTimeFourierIntegrand, mul_smul, v, f] using
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi (norm_nonneg _)) (norm_nonneg (χout x))

/-- The original retarded test action, with the source mask before the uncut
spacetime multiplier and the output mask after the spatial evolution.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
def retardedPhysical (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (a : ℝ) (u : graphTestSpace (d + 1) q) (x : E) : V :=
  χout x • ∫ s in a..x 0, graphOperator (Ψ (x 0) s)
    (fun y _ η ↦ b (x 0) s y η)
    (physicalMultiplierSlice β (graphTestToSchwartz (complexSourceMaskTest χsource hs u)) s)
    (spatialPart x)

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
