module
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame
@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open JanetCartan
namespace JanetCartan.CurrentGeometricNeighborhood
/-- The flat metric fixes the differential norm in
`app:ch_seed:setup:seed-current`. -/
theorem norm_reference_fderiv {n : ℕ} (G : FlatReference n) (x v : Euclidean n) :
    ‖fderiv ℝ G.map x v‖ = ‖v‖ := by
  have he : ‖fderiv ℝ G.map x v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, fderiv_eq_sum_partialDeriv,
      inner_sum, EuclideanSpace.norm_sq_eq]
    simp_rw [sum_inner, inner_smul_left, inner_smul_right]
    simp only [starRingEnd_apply, star_trivial]
    change (∑ i, ∑ j, v j * (v i * inducedMetric G.map x j i)) = _
    simp [G.inducedMetric_eq_one, Matrix.one_apply, Real.norm_eq_abs, pow_two]
  nlinarith [norm_nonneg (fderiv ℝ G.map x v), norm_nonneg v]


/-- A derivative error below one half preserves the actual metric energy
with constant one quarter (`app:ch_seed:setup:seed-current`). -/
theorem metric_gap_of_fderiv_close {n : ℕ} (G : FlatReference n)
    (F : Euclidean n → Euclidean (embeddingDimension n)) (x : Euclidean n)
    (hclose : ‖fderiv ℝ F x - fderiv ℝ G.map x‖ < 1 / 2) :
    Function.Injective (fderiv ℝ F x) ∧
      ∀ v, (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2 := by
  have hlower (v : Euclidean n) : ‖v‖ / 2 ≤ ‖fderiv ℝ F x v‖ := by
    have he := (fderiv ℝ F x - fderiv ℝ G.map x).le_opNorm v
    have ht := norm_sub_norm_le (fderiv ℝ G.map x v) (fderiv ℝ F x v)
    rw [norm_reference_fderiv] at ht
    have he' : ‖fderiv ℝ G.map x v - fderiv ℝ F x v‖ ≤ (1 / 2 : ℝ) * ‖v‖ := by
      rw [norm_sub_rev]
      exact he.trans (mul_le_mul_of_nonneg_right hclose.le (norm_nonneg _))
    linarith
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    have h := hlower v
    rw [hv, norm_zero] at h
    exact norm_eq_zero.mp (by linarith [norm_nonneg v])
  · intro v
    have h := hlower v
    nlinarith [norm_nonneg v, norm_nonneg (fderiv ℝ F x v)]

end JanetCartan.CurrentGeometricNeighborhood
