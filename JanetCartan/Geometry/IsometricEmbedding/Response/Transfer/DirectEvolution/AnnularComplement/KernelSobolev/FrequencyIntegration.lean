module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.RadialPrecision

/-!
# Integration of the annular source-kernel profile

The full physical-frequency step of `app:ch_response:lem:energy-carrier-jets`
and `app:ch_response:eq:direct-envelope-profile`. The producer is
`AnnularComplement.SourceBounds`, applied separately to the physical kernel and
to the kernel multiplied by the actual output demodulator. The Fourier
normalization is already part of the supplied kernel. No frequency truncation
or remainder estimate is an input.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open LowEnvelope

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Full-frequency integrability and arbitrary precision for one actual kernel
jet in `app:ch_response:lem:energy-carrier-jets`. All scale losses precede `N`;
the integration order and constant precede the family index and scales.
Consumer: the joint jets of the integrated annular complement. -/
theorem exists_annular_integral_precision (s ell b : ℕ) (dLoss Q : ℝ)
    {ν : ℝ} (hν : 0 < ν) (hνlt : ν < 1) (C : ℕ → ℝ) (hC : ∀ N, 0 ≤ C N) :
    ∃ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ (lam L K A : ℝ),
      1 ≤ lam → 1 ≤ L → L ≤ K → K ≤ lam ^ (1 - ν) → 0 ≤ A →
      ∀ f : Euclidean n → F, AEStronglyMeasurable f volume →
      (∀ ξ, ‖f ξ‖ ≤ C N * A * lam ^ dLoss * L ^ ell * K ^ b *
        (lam + ‖ξ‖) ^ s * (K / (lam + ‖ξ‖)) ^ N) →
      Integrable f volume ∧ ‖∫ ξ, f ξ‖ ≤ D * A * lam ^ (-Q) := by
  obtain ⟨N, _, hN⟩ := exists_annular_radial_precision n s ell b dLoss Q hν hνlt
  refine ⟨N, C N * lowEnvelopeRadialMass n,
    mul_nonneg (hC N) (lowEnvelopeRadialMass_nonneg n), ?_⟩
  intro lam L K A hlam hL hLK hK hA f hm hb
  obtain ⟨hi, hbound⟩ := hN lam L K hlam hL hLK hK
  have hmajor : Integrable (fun ξ : Euclidean n ↦
      (C N * A * lam ^ dLoss * L ^ ell * K ^ b) *
        ((lam + ‖ξ‖) ^ s * (K / (lam + ‖ξ‖)) ^ N)) := hi.const_mul _
  have hdom (ξ : Euclidean n) : ‖f ξ‖ ≤
      (C N * A * lam ^ dLoss * L ^ ell * K ^ b) *
        ((lam + ‖ξ‖) ^ s * (K / (lam + ‖ξ‖)) ^ N) := by
    simpa only [mul_assoc] using hb ξ
  refine ⟨hmajor.mono' hm (ae_of_all _ hdom), ?_⟩
  calc
    _ ≤ ∫ ξ : Euclidean n,
        (C N * A * lam ^ dLoss * L ^ ell * K ^ b) *
          ((lam + ‖ξ‖) ^ s * (K / (lam + ‖ξ‖)) ^ N) :=
      norm_integral_le_of_norm_le hmajor (ae_of_all _ hdom)
    _ = C N * A * (lam ^ dLoss * L ^ ell * K ^ b *
        (∫ ξ : Euclidean n, (lam + ‖ξ‖) ^ s * (K / (lam + ‖ξ‖)) ^ N)) := by
      rw [integral_const_mul]; ring
    _ ≤ C N * A * (lowEnvelopeRadialMass n * lam ^ (-Q)) :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg (hC N) hA)
    _ = _ := by ring

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
