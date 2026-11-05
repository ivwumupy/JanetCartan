module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.AveragedMixed.Basic
public import JanetCartan.Analysis.Operator.InverseStability
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# An explicit radius for the averaged inverse

The quantitative segment argument in `app:ch_response:thm:response-literal-transfer`.
The input is the derivative bound on the primitive mixed operator on a convex
covector chart, not a bound on its average. The operator norm is used throughout.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace JanetCartan.ResponseTransfer

/-- A single radius, chosen from the chart buffer and the primitive constants,
for the near-carrier selection in `app:ch_response:thm:response-literal-transfer`.
It does not depend on the carrier frequency. -/
def averagedMixedSelectorRadius (b M K : ℝ) : ℝ :=
  min b (1 / (2 * (M + 1) * (K + 1)))

/-- Positivity of the explicit selector radius
(`app:ch_response:thm:response-literal-transfer`). -/
theorem averagedMixedSelectorRadius_pos {b M K : ℝ}
    (hb : 0 < b) (hM : 0 ≤ M) (hK : 0 ≤ K) :
    0 < averagedMixedSelectorRadius b M K := by
  unfold averagedMixedSelectorRadius
  exact lt_min hb (by positivity)

/-- The explicit radius gives the half-size inverse perturbation budget
(`app:ch_response:thm:response-literal-transfer`). -/
theorem averagedMixedSelectorRadius_small {b M K : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) :
    M * K * averagedMixedSelectorRadius b M K ≤ 1 / 2 := by
  have hden : 0 < 2 * (M + 1) * (K + 1) := by positivity
  calc
    _ ≤ M * K * (1 / (2 * (M + 1) * (K + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg hM hK)
    _ ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ hden]
      nlinarith

/-- A derivative bound on a convex chart controls the actual segment average.
This is the closeness argument for `B` in
`app:ch_response:thm:response-literal-transfer`; it assumes no average estimate. -/
theorem norm_segmentAverage_sub_le {n : ℕ}
    {A : Euclidean n → (Euclidean n →L[ℝ] Euclidean n)}
    {D : Set (Euclidean n)} (hD : Convex ℝ D)
    (hA : ∀ η ∈ D, DifferentiableAt ℝ A η)
    {K : ℝ} (hK : 0 ≤ K) (hd : ∀ η ∈ D, ‖fderiv ℝ A η‖ ≤ K)
    {ζ ε : Euclidean n} (hζ : ζ ∈ D) (hε : ζ + ε ∈ D) :
    ‖(∫ t in (0 : ℝ)..1, A (ζ + t • ε)) - A ζ‖ ≤ K * ‖ε‖ := by
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, ζ + t • ε ∈ D :=
    fun _ ht ↦ hD.add_smul_mem hζ hε ht
  have hc : ContinuousOn (fun t : ℝ ↦ A (ζ + t • ε)) (Icc 0 1) := by
    intro t ht
    exact ((hA _ (hmem t ht)).continuousAt.comp (f := fun s : ℝ ↦ ζ + s • ε)
      (continuousAt_const.add (continuousAt_id.smul continuousAt_const))).continuousWithinAt
  have hi : IntervalIntegrable (fun t : ℝ ↦ A (ζ + t • ε)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hc
  have he : (∫ t in (0 : ℝ)..1, A (ζ + t • ε)) - A ζ =
      ∫ t in (0 : ℝ)..1, (A (ζ + t • ε) - A ζ) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
    simp
  rw [he]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := K * ‖ε‖) (fun t ht ↦ by
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using uIoc_subset_uIcc ht
      calc
        ‖A (ζ + t • ε) - A ζ‖ ≤ K * ‖ζ + t • ε - ζ‖ :=
          hD.norm_image_sub_le_of_norm_fderiv_le hA hd hζ (hmem t ht')
        _ = K * (t * ‖ε‖) := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht'.1]
        _ ≤ K * ‖ε‖ := mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_left (norm_nonneg _) ht'.2) hK)

/-- Uniform invertibility of the actual segment average on the explicit
selector. Only the central inverse and primitive derivative are assumed
(`app:ch_response:thm:response-literal-transfer`). The chart and constants
may be shared over arbitrary compact physical and carrier supports. -/
theorem segmentAverage_inverse_on_selector {n : ℕ}
    {A : Euclidean n → (Euclidean n →L[ℝ] Euclidean n)}
    {D : Set (Euclidean n)} (hD : Convex ℝ D)
    (hA : ∀ η ∈ D, DifferentiableAt ℝ A η)
    {ζ : Euclidean n} {b M K : ℝ} (hb : 0 < b)
    (hbuffer : Metric.closedBall ζ b ⊆ D)
    (hu : IsUnit (A ζ)) (hM : ‖Ring.inverse (A ζ)‖ ≤ M)
    (hK : 0 ≤ K) (hd : ∀ η ∈ D, ‖fderiv ℝ A η‖ ≤ K)
    {ε : Euclidean n} (hε : ‖ε‖ ≤ averagedMixedSelectorRadius b M K) :
    IsUnit (∫ t in (0 : ℝ)..1, A (ζ + t • ε)) ∧
      ‖Ring.inverse (∫ t in (0 : ℝ)..1, A (ζ + t • ε))‖ ≤ 2 * M := by
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans hM
  have hζ : ζ ∈ D := hbuffer (Metric.mem_closedBall_self hb.le)
  have hend : ζ + ε ∈ D := by
    apply hbuffer
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hε.trans (min_le_left _ _)
  have hgap := norm_segmentAverage_sub_le hD hA hK hd hζ hend
  have hsmall : M * ‖(∫ t in (0 : ℝ)..1, A (ζ + t • ε)) - A ζ‖ ≤ 1 / 2 := by
    calc
      _ ≤ M * (K * ‖ε‖) := mul_le_mul_of_nonneg_left hgap hM₀
      _ ≤ M * K * averagedMixedSelectorRadius b M K := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hε (mul_nonneg hM₀ hK)
      _ ≤ _ := averagedMixedSelectorRadius_small hM₀ hK
  exact (OperatorInverse.inverse_stability_half _ _ hu hM hsmall).imp_right And.left

end JanetCartan.ResponseTransfer
