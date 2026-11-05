module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Assembly

/-!
# Finite channel normals on the continuum input spaces

The direct-sum row in `app:ch_background:defn:bg-row` has the sum of the
channel normals. This connects the individually constructed image and carrier
operators to the normal-reduction consumer without choosing a second row.
The exterior summand is literally multiplication by `(1 - ψ)²`.

These are algebraic statements about the published operators. Actual carrier
instantiation is still needed before applying them to the geometric family.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumRow

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The finite carrier normal is the sum of its channel normals, with no cross
terms between independent input slots (`app:ch_background:defn:bg-row`). -/
theorem carrierRow_normal (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    carrierRow T ∘L (carrierRow T).adjoint =
      ∑ a, carrierChannel (T a) ∘L (carrierChannel (T a)).adjoint := by
  ext1 w
  simp [ContinuousLinearMap.comp_apply, carrierRow_adjoint_apply]

/-- The image and carrier inputs are orthogonal Hilbert slots, so their
normals add (`app:ch_background:defn:bg-row`). -/
theorem physicalRow_normal (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    physicalRow image T ∘L (physicalRow image T).adjoint =
      image ∘L image.adjoint +
        ∑ a, carrierChannel (T a) ∘L (carrierChannel (T a)).adjoint := by
  rw [← carrierRow_normal]
  ext1 w
  simp [ContinuousLinearMap.comp_apply, physicalRow_adjoint_apply]

/-- Squaring the exterior operator is multiplication by the literal squared
complement (`app:ch_background:prop:bg-frame`, Step 4). -/
theorem exteriorChannel_comp_self (ψ : C(Torus n, ℝ)) :
    exteriorChannel ψ ∘L exteriorChannel ψ = cutoffMultiplier ((1 - ψ) ^ 2) := by
  ext1 f
  apply Lp.ext
  filter_upwards [exteriorChannel_coeFn ψ (exteriorChannel ψ f),
    exteriorChannel_coeFn ψ f, cutoffMultiplier_coeFn ((1 - ψ) ^ 2) f] with x h₁ h₂ h₃
  change exteriorChannel ψ (exteriorChannel ψ f) x = _
  rw [h₁, h₂, h₃, smul_smul]
  congr 1
  simp [pow_two]

/-- Exact global row normal used by normal reduction and elliptic bootstrap
(`app:ch_background:prop:bg-frame`). Each reflected carrier PDO normal already
contains the factor four; substituting it into this sum adds no further factor. -/
theorem augmentedNormal_eq_sum (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ)) :
    augmentedNormal image T ψ = image ∘L image.adjoint +
      (∑ a, carrierChannel (T a) ∘L (carrierChannel (T a)).adjoint) +
        cutoffMultiplier ((1 - ψ) ^ 2) := by
  rw [← physicalRow_normal, ← exteriorChannel_comp_self]
  ext1 w
  simp [augmentedNormal, ContinuousLinearMap.comp_apply, augmentedRow_adjoint_apply]

/-- The factor four is present once when the normal is expressed using the
complex carriers (`app:ch_background:eq:bg-realification`). -/
theorem augmentedNormal_eq_complex_normals (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ)) :
    augmentedNormal image T ψ = image ∘L image.adjoint +
      (∑ a, (4 : ℝ) • realOutputCompression (T a ∘L (T a).adjoint)) +
        cutoffMultiplier ((1 - ψ) ^ 2) := by
  rw [augmentedNormal_eq_sum]
  simp_rw [carrierChannel_normal]

/-- The carrier row is bounded by the finite sum of twice the complex channel
norms on the actual Hilbert sum (`app:ch_background:prop:bg-frame`). -/
theorem carrierRow_norm_le (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    ‖carrierRow T‖ ≤ ∑ a, 2 * ‖T a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [carrierRow_apply, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  exact ((carrierChannel (T a)).le_opNorm (f a)).trans
    (mul_le_mul (carrierChannel_norm_le (T a)) (PiLp.norm_apply_le f a)
      (norm_nonneg _) (by positivity))

/-- A finite collection of constructed channel bounds gives the physical-row
bound, with the original Hilbert input norm (`app:ch_background:prop:bg-frame`). -/
theorem physicalRow_norm_le (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    ‖physicalRow image T‖ ≤ ‖image‖ + ∑ a, 2 * ‖T a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [physicalRow_apply, add_mul]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (image.le_opNorm f.fst).trans
      (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le _ f) (norm_nonneg _))
  · exact ((carrierRow T).le_opNorm f.snd).trans
      (mul_le_mul (carrierRow_norm_le T) (WithLp.norm_snd_le _ f)
        (norm_nonneg _) (by positivity))

/-- The full augmented row is bounded on its stated input space; geometric
uniformity follows once the finitely many actual channel bounds are supplied
(`app:ch_background:prop:bg-frame`). -/
theorem augmentedRow_norm_le (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ)) :
    ‖augmentedRow image T ψ‖ ≤ ‖image‖ + (∑ a, 2 * ‖T a‖) + ‖1 - ψ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [augmentedRow_apply, add_mul]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact ((physicalRow image T).le_opNorm f.fst).trans
      (mul_le_mul (physicalRow_norm_le image T) (WithLp.norm_fst_le _ f)
        (norm_nonneg _) (by positivity))
  · exact ((exteriorChannel ψ).le_opNorm f.snd).trans
      (mul_le_mul (exteriorChannel_norm_le ψ) (WithLp.norm_snd_le _ f)
        (norm_nonneg _) (norm_nonneg _))

end JanetCartan.ContinuumRow
