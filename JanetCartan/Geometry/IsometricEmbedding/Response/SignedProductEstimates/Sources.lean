module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.ProductSum.Algebra
public import JanetCartan.Geometry.IsometricEmbedding.Response.SourceExtension.Complex
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Frobenius
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.Basic

/-!
# Exact signed sources at their true frequencies

The substitution in Step 1 of `app:ch_pairs:prop:pairs-lag-sum` uses the full
tensor amplitudes and the original source cutoff. The identities below connect
`ProductSum.plusSource` and `ProductSum.minusSource` to the existing
`SourceNegative.modulatedSource`, including its physical frequency convention.
The same real response can therefore be used on the real quadrature. Phase or
amplitude extensions need agree only on the entire source support; there is no
selection of a different response or of different samples.
-/

@[expose] public noncomputable section

open Set
open scoped ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.SignedProductEstimates

open ResponseTransfer ResponseTransfer.SourceNegative ResponseSourceExtension

variable {n N : ℕ} {ι : Type*}

private theorem carrier_div_eq_wavePhase (θ : Euclidean n → ℝ) {ρ : ℝ}
    (hρ : ρ ≠ 0) (x : Euclidean n) :
    carrier ρ (fun y ↦ θ y / ρ) x = wavePhase (θ x) := by
  simp only [carrier, wavePhase, mul_div_cancel₀ (θ x) hρ]
  congr 1
  field_simp

/-- The full plus source, including the doubled diagonal, is the real
quadrature of the existing modulated source at any nonzero true frequency
(`app:ch_pairs:eq:pairs-lag-one-error`). No source cutoff is dropped. -/
theorem cutoff_plusSource_eq_real_modulatedSource
    (χ : Euclidean n → ℝ) (θ : ι → Euclidean n → ℝ)
    (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (i j : ι) {ρ : ℝ} (hρ : ρ ≠ 0) :
    (fun x ↦ χ x • ProductSum.plusSource θ A i j x) =
      tensorFieldRealPart (modulatedSource χ (fun x ↦ (θ i x + θ j x) / ρ)
        (fun x ↦ symmetricBilinearTensor (A i x) (A j x)) ρ) := by
  ext x a b
  change χ x * (wavePhase (θ i x + θ j x) *
    symmetricBilinearTensor (A i x) (A j x) a b).re =
      (χ x • (carrier ρ (fun y ↦ (θ i y + θ j y) / ρ) x *
        symmetricBilinearTensor (A i x) (A j x) a b)).re
  rw [carrier_div_eq_wavePhase (fun y ↦ θ i y + θ j y) hρ]
  simp

/-- The full minus source uses the conjugate of the second ACTUAL amplitude
at its normalized difference phase (`app:ch_pairs:lem:pairs-ledger`). Its
nonzero true frequency will come from distinct separated samples. -/
theorem cutoff_minusSource_eq_real_modulatedSource
    (χ : Euclidean n → ℝ) (θ : ι → Euclidean n → ℝ)
    (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (i j : ι) {ρ : ℝ} (hρ : ρ ≠ 0) :
    (fun x ↦ χ x • ProductSum.minusSource θ A i j x) =
      tensorFieldRealPart (modulatedSource χ (fun x ↦ (θ i x - θ j x) / ρ)
        (fun x ↦ symmetricBilinearTensor (A i x) ((A j x).map conj)) ρ) := by
  ext x a b
  change χ x * (wavePhase (θ i x - θ j x) *
    symmetricBilinearTensor (A i x) ((A j x).map conj) a b).re =
      (χ x • (carrier ρ (fun y ↦ (θ i y - θ j y) / ρ) x *
        symmetricBilinearTensor (A i x) ((A j x).map conj) a b)).re
  rw [carrier_div_eq_wavePhase (fun y ↦ θ i y - θ j y) hρ]
  simp

/-- Supported phase and amplitude substitution preserves the literal complex
source in `app:ch_pairs:prop:pairs-lag-sum`, Step 1. This is the exact boundary
between the retained local tensors and the global analytic representatives.
The same identity covers the reduced vector fiber without changing cutoffs. -/
theorem modulatedSource_eq_of_support_agreement
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (χ φ ψ : Euclidean n → ℝ) (a b : Euclidean n → F) (ρ : ℝ)
    (hφ : EqOn φ ψ (tsupport χ)) (ha : EqOn a b (tsupport χ)) :
    modulatedSource χ φ a ρ = modulatedSource χ ψ b ρ := by
  funext x
  by_cases hx : χ x = 0
  · simp [modulatedSource, hx]
  · have hs := subset_tsupport χ hx
    simp only [modulatedSource, carrier, hφ hs, ha hs]

/-- Any extensions agreeing on the FULL source support give the same plus
source through the same `B` (`app:ch_pairs:eq:pairs-weighted-U`). The cutoff
stays inside the response; the actual tensor is never replaced by its leading
part, and equal sample indices are allowed. -/
theorem response_cutoff_plusSource_eq_real_modulatedSource
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (χ : Euclidean n → ℝ) (θ : ι → Euclidean n → ℝ)
    (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (i j : ι) {ρ : ℝ} (hρ : ρ ≠ 0)
    (φ : Euclidean n → ℝ) (a : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hφ : EqOn (fun x ↦ (θ i x + θ j x) / ρ) φ (tsupport χ))
    (ha : EqOn (fun x ↦ symmetricBilinearTensor (A i x) (A j x)) a (tsupport χ)) :
    B (fun x ↦ χ x • ProductSum.plusSource θ A i j x) =
      fun x ↦ WithLp.toLp 2 (fun l ↦ (complexifyResponse B
        (modulatedSource χ φ a ρ) x l).re) := by
  rw [cutoff_plusSource_eq_real_modulatedSource χ θ A i j hρ,
    modulatedSource_eq_of_support_agreement χ _ φ _ a ρ hφ ha]
  ext x l
  exact (complexifyResponse_re B _ x l).symm

/-- Supported substitution for the same fixed response to the full minus
source (`app:ch_pairs:eq:pairs-weighted-U`). No estimate for the unused
difference diagonal is needed by this identity. -/
theorem response_cutoff_minusSource_eq_real_modulatedSource
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (χ : Euclidean n → ℝ) (θ : ι → Euclidean n → ℝ)
    (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (i j : ι) {ρ : ℝ} (hρ : ρ ≠ 0)
    (φ : Euclidean n → ℝ) (a : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hφ : EqOn (fun x ↦ (θ i x - θ j x) / ρ) φ (tsupport χ))
    (ha : EqOn (fun x ↦ symmetricBilinearTensor (A i x) ((A j x).map conj))
      a (tsupport χ)) :
    B (fun x ↦ χ x • ProductSum.minusSource θ A i j x) =
      fun x ↦ WithLp.toLp 2 (fun l ↦ (complexifyResponse B
        (modulatedSource χ φ a ρ) x l).re) := by
  rw [cutoff_minusSource_eq_real_modulatedSource χ θ A i j hρ,
    modulatedSource_eq_of_support_agreement χ _ φ _ a ρ hφ ha]
  ext x l
  exact (complexifyResponse_re B _ x l).symm

end JanetCartan.SignedProductEstimates
