module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ImagePerturbation
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FiniteNormal

/-!
# Perturbation of the existing finite augmented normal

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, the fixed exterior
square cancels and the finite carrier *normal* differences add. The image
difference is bounded by its actual coefficient formula. The complex carrier
normals must be compared by their full amplitudes on common inverse charts;
no continuity of the oscillatory rows is used or asserted here.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumNormal

open ContinuumRow

variable {n : ℕ} {ι : Type*} [Fintype ι]

set_option maxHeartbeats 600000 in
/-- The same finite row and exterior square reduce comparison to image and
complex carrier normals, with the real-quadrature factor four exactly once.
Source: `paper-v2.tex`, `app:ch_background:prop:bg-frame`. -/
theorem norm_augmentedNormal_sub_le_channel_normals
    (image image₀ : OutputL2 n →L[ℝ] OutputL2 n)
    (T T₀ : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ)) :
    ‖augmentedNormal image T ψ - augmentedNormal image₀ T₀ ψ‖ ≤
      ‖NormalPerturbation.normal image - NormalPerturbation.normal image₀‖ +
        4 * ∑ a, ‖T a ∘L (T a).adjoint - T₀ a ∘L (T₀ a).adjoint‖ := by
  have heq : augmentedNormal image T ψ - augmentedNormal image₀ T₀ ψ =
      (NormalPerturbation.normal image - NormalPerturbation.normal image₀) +
        ∑ a, (4 : ℝ) • realOutputCompression
          (T a ∘L (T a).adjoint - T₀ a ∘L (T₀ a).adjoint) := by
    rw [augmentedNormal_eq_complex_normals, augmentedNormal_eq_complex_normals]
    simp only [realOutputCompression_sub, smul_sub, Finset.sum_sub_distrib,
      NormalPerturbation.normal]
    abel
  rw [heq]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  exact mul_le_mul_of_nonneg_left (realOutputCompression_norm_le _) (by norm_num)

/-- The image contribution is discharged from the coefficient arrays in the
finite augmented comparison (`paper-v2.tex`, `app:ch_background:prop:bg-frame`).
The remaining explicit terms are differences of the literal uncut complex
carrier normals, rather than differences of their oscillatory rows. -/
theorem norm_augmentedNormal_sub_le_coefficients_and_carriers
    (c d : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (T T₀ : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    ‖augmentedNormal (imageChannel c χmeas χsrc) T ψ -
        augmentedNormal (imageChannel d χmeas χsrc) T₀ ψ‖ ≤
      2 * (‖χmeas‖ * reducedCoefficientBound d * ‖χsrc‖) *
        (‖χmeas‖ * reducedCoefficientBound (c - d) * ‖χsrc‖) +
      (‖χmeas‖ * reducedCoefficientBound (c - d) * ‖χsrc‖) ^ 2 +
        4 * ∑ a, ‖T a ∘L (T a).adjoint - T₀ a ∘L (T₀ a).adjoint‖ :=
  (norm_augmentedNormal_sub_le_channel_normals _ _ T T₀ ψ).trans
    (add_le_add (norm_imageNormal_sub_le c d χmeas χsrc) le_rfl)

end JanetCartan.ContinuumNormal
