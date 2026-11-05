module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.Geometry

/-!
# The separate metric and normal inverse bounds

The two gaps in `app:ch_seed:setup:seed-current` control distinct inverse
operators. The metric gap is never substituted for the normal gap.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open JanetCartan.AmbientResponse

namespace JanetCartan.ProjectedStressFrame

/-- A finite-dimensional energy lower bound gives an actual inverse and its
operator norm bound, used for both gaps in `app:ch_seed:setup:seed-current`. -/
theorem isUnit_and_norm_inverse_le_of_energy {d : ℕ}
    (T : Euclidean d →L[ℝ] Euclidean d) {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ v, ‖v‖ ^ 2 ≤ C * inner ℝ v (T v)) :
    IsUnit T ∧ ‖Ring.inverse T‖ ≤ C := by
  have hlower (v : Euclidean d) : ‖v‖ ≤ C * ‖T v‖ := by
    have h := (henergy v).trans
      (mul_le_mul_of_nonneg_left (real_inner_le_norm v (T v)) hC)
    by_cases hv : ‖v‖ = 0
    · rw [hv]; positivity
    · have hvpos := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
      nlinarith
  have hinj : Function.Injective T := by
    apply (injective_iff_map_eq_zero T).mpr
    intro v hv
    have h := hlower v
    rw [hv, norm_zero, mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  have hu : IsUnit T := by
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  refine ⟨hu, (Ring.inverse T).opNorm_le_bound hC ?_⟩
  intro v
  have hmul : T (Ring.inverse T v) = v :=
    congrArg (fun A : Euclidean d →L[ℝ] Euclidean d ↦ A v)
      (Ring.mul_inverse_cancel T hu)
  simpa only [hmul] using hlower (Ring.inverse T v)

/-- The operator representing the induced metric is `(dF)* dF`, from
`app:ch_seed:setup:seed-current`. This uses Euclidean operator norms. -/
def metricOperator {n N : ℕ} (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    Euclidean n →L[ℝ] Euclidean n :=
  (fderiv ℝ F x).adjoint.comp (fderiv ℝ F x)

/-- The Euclidean metric operator has exactly the induced metric as its
coordinate matrix, in `app:ch_seed:setup:seed-current`. -/
theorem metricOperator_entry {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (i j : Fin n) :
    inner ℝ (EuclideanSpace.single i 1)
      (metricOperator F x (EuclideanSpace.single j 1)) = inducedMetric F x i j := by
  rw [metricOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- The metric gap alone bounds the inverse metric by `κ_met⁻¹`, as in
`app:ch_seed:setup:seed-current`. -/
theorem metricOperator_inverse_bound {n N : ℕ} {F : Euclidean n → Euclidean N}
    {x : Euclidean n} {κmet : ℝ} (hκmet : 0 < κmet)
    (hgap : ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) :
    IsUnit (metricOperator F x) ∧ ‖Ring.inverse (metricOperator F x)‖ ≤ κmet⁻¹ := by
  apply isUnit_and_norm_inverse_le_of_energy _ (inv_nonneg.mpr hκmet.le)
  intro v
  have he : inner ℝ v (metricOperator F x v) = ‖fderiv ℝ F x v‖ ^ 2 := by
    rw [metricOperator, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [he]
  exact (le_inv_mul_iff₀ hκmet).mpr (hgap v)

/-- The energy of `A_F = BB* + P_tan` splits into the two orthogonal terms
in `app:ch_seed:setup:seed-current`. -/
theorem ambientNormalOperator_energy {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (w : Euclidean N) :
    inner ℝ w (ambientNormalOperator F x w) =
      ‖normalPairing F (fun _ ↦ w) x‖ ^ 2 + ‖tangentProjection F x w‖ ^ 2 := by
  change inner ℝ w ((normalMapLinear F x) ((normalMapLinear F x).adjoint w) +
    tangentProjection F x w) = _
  rw [inner_add_right, ← LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
    adjoint_normalMapLinear]
  congr 1
  rw [real_inner_comm]
  exact (LinearMap.range (fderiv ℝ F x).toLinearMap).re_inner_starProjection_eq_normSq w

/-- The least normal singular-value gap gives the bound
`‖A_F⁻¹‖ ≤ max(1, κ⁻²)` in `app:ch_seed:setup:seed-current`.
The gap is imposed only on normal vectors, and no metric gap is used. -/
theorem ambientNormalOperator_inverse_bound {n N : ℕ} {F : Euclidean n → Euclidean N}
    {x : Euclidean n} {κ : ℝ} (hκ : 0 < κ)
    (hgap : ∀ w ∈ normalSpace F x,
      κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) :
    IsUnit (ambientNormalOperator F x) ∧
      ‖Ring.inverse (ambientNormalOperator F x)‖ ≤ max 1 (κ ^ 2)⁻¹ := by
  apply isUnit_and_norm_inverse_le_of_energy _ (zero_le_one.trans (le_max_left _ _))
  intro w
  have hg := hgap (normalProjection F x w) (normalProjection_mem_normalSpace F x w)
  have hp : normalPairing F (fun _ ↦ normalProjection F x w) x =
      normalPairing F (fun _ ↦ w) x := normalPairing_normalProjection F (fun _ ↦ w) x
  rw [hp] at hg
  have hgsq : κ ^ 2 * ‖normalProjection F x w‖ ^ 2 ≤
      ‖normalPairing F (fun _ ↦ w) x‖ ^ 2 := by
    simpa only [mul_pow] using (sq_le_sq₀
      (mul_nonneg hκ.le (norm_nonneg _)) (norm_nonneg _)).mpr hg
  have hn := (le_inv_mul_iff₀ (sq_pos_of_pos hκ)).mpr hgsq
  have hn' := hn.trans (mul_le_mul_of_nonneg_right (le_max_right 1 (κ ^ 2)⁻¹)
    (sq_nonneg ‖normalPairing F (fun _ ↦ w) x‖))
  have ht := mul_le_mul_of_nonneg_right (le_max_left 1 (κ ^ 2)⁻¹)
    (sq_nonneg ‖tangentProjection F x w‖)
  have hsplit := (LinearMap.range (fderiv ℝ F x).toLinearMap).norm_sq_eq_add_norm_sq_starProjection w
  change ‖w‖ ^ 2 = ‖tangentProjection F x w‖ ^ 2 +
    ‖normalProjection F x w‖ ^ 2 at hsplit
  rw [ambientNormalOperator_energy, hsplit]
  nlinarith

end JanetCartan.ProjectedStressFrame
