module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.SourceKernel

/-!
# The full reverse source phase

For `app:ch_response:thm:response-literal-transfer`, the reverse estimate must
use the full nonlinear inverse-chart gap. This file identifies that covector
and shows that the gap persists under the low input Fourier frequency. It does
not replace the inverse-chart hypothesis by separation of `η` from the carrier.
-/

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer.LowEnvelope

/-- The exact derivative of the nonlinear reverse source phase in
`app:ch_response:thm:response-literal-transfer`. -/
theorem fderiv_reverseSourcePhase {n : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ) (ρ : ℝ)
    (y η θ x : Euclidean n) (hS : DifferentiableAt ℝ (fun z ↦ S z η) x)
    (hφ : DifferentiableAt ℝ φ x) :
    fderiv ℝ (reverseSourcePhase S φ ρ y η θ) x =
      ρ • fderiv ℝ φ x - fderiv ℝ (fun z ↦ S z η) x + innerSL ℝ θ := by
  have h := ((hS.hasFDerivAt.const_sub (inner ℝ y η)).add
    (hφ.hasFDerivAt.const_mul ρ)).add (innerSL ℝ θ).hasFDerivAt
  have heq : reverseSourcePhase S φ ρ y η θ =
      fun z ↦ inner ℝ y η - S z η + ρ * φ z + inner ℝ θ z := by
    funext z
    simp only [reverseSourcePhase, real_inner_comm θ z]
  rw [heq]
  calc
    _ = -fderiv ℝ (fun z ↦ S z η) x + ρ • fderiv ℝ φ x + innerSL ℝ θ := by
      simpa only [Pi.add_def, coe_innerSL_apply] using h.fderiv
    _ = _ := by abel

/-- The full inverse-chart gap survives the low Fourier input in
`app:ch_response:thm:response-literal-transfer`. The inverse-chart geometry is
an explicit producer input; this is a consequence of that input, not its proof. -/
theorem reverseSourcePhase_gap {n : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    {ρ c : ℝ} (hc : 0 ≤ c) (y η θ x : Euclidean n)
    (hS : DifferentiableAt ℝ (fun z ↦ S z η) x)
    (hφ : DifferentiableAt ℝ φ x)
    (hgap : c * (ρ + ‖η‖) ≤ ‖ρ • fderiv ℝ φ x - fderiv ℝ (fun z ↦ S z η) x‖)
    (hθ : ‖θ‖ ≤ c * ρ / 2) :
    (c / 2) * (ρ + ‖η‖) ≤ ‖fderiv ℝ (reverseSourcePhase S φ ρ y η θ) x‖ := by
  rw [fderiv_reverseSourcePhase S φ ρ y η θ x hS hφ]
  have hh := norm_sub_norm_le
    (ρ • fderiv ℝ φ x - fderiv ℝ (fun z ↦ S z η) x) (-(innerSL ℝ θ))
  rw [norm_neg, innerSL_apply_norm, sub_neg_eq_add] at hh
  nlinarith [mul_nonneg hc (norm_nonneg η)]

end JanetCartan.ResponseTransfer.LowEnvelope
