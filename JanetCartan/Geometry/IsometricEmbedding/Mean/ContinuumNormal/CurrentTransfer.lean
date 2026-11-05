module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FinitePerturbation

/-!
# Transfer of the augmented gap under an actual normal comparison

The frozen and current rows use the same exterior cutoff.  Hence their
augmented-normal difference is exactly the physical-normal difference, and an
operator-norm estimate for that difference transfers the frozen quadratic gap.
This is the algebraic bridge consumed by the eventual same-family row and
carrier-normal construction; it makes no claim that either comparison estimate
has been constructed.
-/

@[expose] public noncomputable section

open scoped InnerProduct

namespace JanetCartan.ContinuumNormal

open ContinuumRow

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-/ `app:ch_background:eq:bg-global-bound`, with the current normal comparison
    supplied as an explicit analytic input. -/
theorem augmented_gap_of_normal_comparison
    (image image₀ : OutputL2 n →L[ℝ] OutputL2 n)
    (T T₀ : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (ψ : C(Torus n, ℝ)) (S : Set (OutputL2 n)) {g ε : ℝ}
    (hgap : ∀ f ∈ S,
      g * ‖f‖ ^ 2 ≤ inner ℝ (augmentedNormal image₀ T₀ ψ f) f)
    (hclose :
      ‖augmentedNormal image T ψ - augmentedNormal image₀ T₀ ψ‖ ≤ ε) :
    ∀ f ∈ S,
      (g - ε) * ‖f‖ ^ 2 ≤ inner ℝ (augmentedNormal image T ψ f) f := by
  intro f hf
  have h := NormalPerturbation.quadratic_lower_bound_of_norm_sub_le
    (augmentedNormal image₀ T₀ ψ) (augmentedNormal image T ψ) S hgap hclose
    f hf
  simpa only [RCLike.re_to_real] using h

/-/ A comparison costing at most half the frozen gap preserves a half-gap. -/
theorem augmented_half_gap_of_normal_comparison
    (image image₀ : OutputL2 n →L[ℝ] OutputL2 n)
    (T T₀ : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (ψ : C(Torus n, ℝ)) (S : Set (OutputL2 n)) {g ε : ℝ}
    (hgap : ∀ f ∈ S,
      g * ‖f‖ ^ 2 ≤ inner ℝ (augmentedNormal image₀ T₀ ψ f) f)
    (hclose :
      ‖augmentedNormal image T ψ - augmentedNormal image₀ T₀ ψ‖ ≤ ε)
    (hε : ε ≤ g / 2) :
    ∀ f ∈ S,
      (g / 2) * ‖f‖ ^ 2 ≤ inner ℝ (augmentedNormal image T ψ f) f := by
  intro f hf
  have h := augmented_gap_of_normal_comparison image image₀ T T₀ ψ S hgap hclose f hf
  have hc : g / 2 ≤ g - ε := by linarith
  exact (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖f‖)).trans h

/-/ The channel-level form exposes the factor four from the two real
    quadratures and is the form used by the concrete image/carrier estimates. -/
theorem augmented_half_gap_of_channel_comparison
    (image image₀ : OutputL2 n →L[ℝ] OutputL2 n)
    (T T₀ : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (ψ : C(Torus n, ℝ)) (S : Set (OutputL2 n)) {g εimage εcarrier : ℝ}
    (hgap : ∀ f ∈ S,
      g * ‖f‖ ^ 2 ≤ inner ℝ (augmentedNormal image₀ T₀ ψ f) f)
    (himage :
      ‖NormalPerturbation.normal image - NormalPerturbation.normal image₀‖ ≤
        εimage)
    (hcarrier :
      ∑ a, ‖T a ∘L (T a).adjoint - T₀ a ∘L (T₀ a).adjoint‖ ≤ εcarrier)
    (hsmall : εimage + 4 * εcarrier ≤ g / 2) :
    ∀ f ∈ S,
      (g / 2) * ‖f‖ ^ 2 ≤ inner ℝ (augmentedNormal image T ψ f) f := by
  apply augmented_half_gap_of_normal_comparison image image₀ T T₀ ψ S hgap
  · exact (norm_augmentedNormal_sub_le_channel_normals image image₀ T T₀ ψ).trans
      (add_le_add himage (mul_le_mul_of_nonneg_left hcarrier (by norm_num)))
  · exact hsmall

end JanetCartan.ContinuumNormal
