module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.Basic
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Inverse Fourier jets from absolute moments

The finite absolute Fourier moments control the pointwise envelope jets needed
for the original-source estimate preceding
`app:ch_response:eq:response-graded-reduced`. The moment hypotheses are produced
from `app:ch_response:eq:response-graded-source` by
`SobolevEnvelopeBounds.fourier_moment_integrable` in `EnvelopeJets.Moments`.
The parent envelope construction supplies those moments and the pointwise
identification with the inverse Fourier integral.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.SourceNegative

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Finite absolute moments bound every pointwise inverse Fourier jet of the
given order, retaining the exact `2π` factor. This supplies the differentiation
step from `app:ch_response:eq:response-graded-source` to the envelope jet bounds
used in the original-source estimate before
`app:ch_response:eq:response-graded-reduced`. -/
theorem norm_iteratedFDeriv_fourierInv_le_moment [CompleteSpace F]
    (g : Euclidean n → F) (r : ℕ)
    (hg : AEStronglyMeasurable g volume)
    (hmom : ∀ j ≤ r, Integrable (fun ξ ↦ ‖ξ‖ ^ j * ‖g ξ‖) volume)
    (x : Euclidean n) :
    ‖iteratedFDeriv ℝ r (𝓕⁻ g) x‖ ≤
      (2 * Real.pi) ^ r * (∫ ξ, ‖ξ‖ ^ r * ‖g ξ‖) := by
  let L : Euclidean n →L[ℝ] Euclidean n →L[ℝ] ℝ := -innerSL ℝ
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro ξ
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro y
    change ‖-inner ℝ ξ y‖ ≤ 1 * ‖ξ‖ * ‖y‖
    simpa only [norm_neg, one_mul] using norm_inner_le_norm ξ y
  have hbase : 2 * Real.pi * ‖L‖ ≤ 2 * Real.pi := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hL
      (by positivity : 0 ≤ 2 * Real.pi)
  have hmom' : ∀ j : ℕ, (j : ℕ∞) ≤ (r : ℕ∞) →
      Integrable (fun ξ ↦ ‖ξ‖ ^ j * ‖g ξ‖) volume := by
    intro j hj
    exact hmom j (by exact_mod_cast hj)
  change ‖iteratedFDeriv ℝ r
    (VectorFourier.fourierIntegral Real.fourierChar volume L.toLinearMap₁₂ g) x‖ ≤ _
  rw [VectorFourier.iteratedFDeriv_fourierIntegral L hmom' hg (le_refl (r : ℕ∞))]
  calc
    ‖VectorFourier.fourierIntegral Real.fourierChar volume L.toLinearMap₁₂
        (fun ξ ↦ VectorFourier.fourierPowSMulRight L g ξ r) x‖
      ≤ ∫ ξ, ‖VectorFourier.fourierPowSMulRight L g ξ r‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ ≤ ∫ ξ, (2 * Real.pi) ^ r * (‖ξ‖ ^ r * ‖g ξ‖) := by
      apply integral_mono
        (VectorFourier.integrable_fourierPowSMulRight L (hmom r le_rfl) hg).norm
        ((hmom r le_rfl).const_mul _)
      intro ξ
      calc
        ‖VectorFourier.fourierPowSMulRight L g ξ r‖
          ≤ (2 * Real.pi * ‖L‖) ^ r * ‖ξ‖ ^ r * ‖g ξ‖ :=
            VectorFourier.norm_fourierPowSMulRight_le L g ξ r
        _ ≤ (2 * Real.pi) ^ r * (‖ξ‖ ^ r * ‖g ξ‖) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase r)
              (by positivity)) (norm_nonneg _)
    _ = (2 * Real.pi) ^ r * (∫ ξ, ‖ξ‖ ^ r * ‖g ξ‖) := integral_const_mul _ _

end JanetCartan.ResponseTransfer.SourceNegative
