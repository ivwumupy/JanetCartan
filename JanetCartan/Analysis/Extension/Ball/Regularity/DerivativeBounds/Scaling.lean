module

public import JanetCartan.Analysis.Extension.Ball.Regularity.DerivativeBounds.Profile

/-!
# Derivative bounds for the collar coordinates

The rescaling in `app:ch_regular_base:eq:extension-radial-formula` is a fixed
smooth coordinate map followed by a linear map of norm at most `2 ^ k`.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace JanetCartan.BallExtension.Parameters

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : JanetCartan.BallExtension.Parameters E)

/-- The unscaled collar coordinates in
`app:ch_regular_base:eq:extension-radial-formula`. -/
def collarCoordinates (x : E) : ℝ × E := (‖x - p.center‖ - p.radius, x)

/-- The scaled collar coordinates in
`app:ch_regular_base:eq:extension-radial-formula`. -/
def scaledCollarCoordinates (k : ℕ) (x : E) : ℝ × E :=
  ((2 : ℝ) ^ k * (‖x - p.center‖ - p.radius), x)

/-- Smoothness of the fixed collar coordinates used in
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem contDiffOn_collarCoordinates :
    ContDiffOn ℝ ∞ p.collarCoordinates {x | p.radius ≤ ‖x - p.center‖} := by
  have hn : ContDiffOn ℝ ∞ (fun x : E ↦ ‖x - p.center‖)
      {x | p.radius ≤ ‖x - p.center‖} :=
    (contDiffOn_id.sub contDiffOn_const).norm ℝ
      (fun _ hx ↦ norm_pos_iff.mp (p.radius_pos.trans_le hx))
  exact (hn.sub contDiffOn_const).prodMk contDiffOn_id

/-- Smoothness of the rescaled coordinates used in
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem contDiffOn_scaledCollarCoordinates (k : ℕ) :
    ContDiffOn ℝ ∞ (p.scaledCollarCoordinates k) {x | p.radius ≤ ‖x - p.center‖} :=
  (contDiffOn_const.mul p.contDiffOn_collarCoordinates.fst).prodMk contDiffOn_id

/-- Compactness bounds the derivatives of the unscaled coordinates in
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem exists_collarCoordinates_derivative_bound [FiniteDimensional ℝ E] (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i ≤ m, ∀ x ∈ p.compactExteriorCollar,
      ‖iteratedFDerivWithin ℝ i p.collarCoordinates
        {y | p.radius ≤ ‖y - p.center‖} x‖ ≤ B := by
  have hb (i : ℕ) : ∃ B : ℝ, ∀ x ∈ p.compactExteriorCollar,
      ‖iteratedFDerivWithin ℝ i p.collarCoordinates
        {y | p.radius ≤ ‖y - p.center‖} x‖ ≤ B :=
    p.isCompact_compactExteriorCollar.exists_bound_of_continuousOn
      ((p.contDiffOn_collarCoordinates.continuousOn_iteratedFDerivWithin
        (by simp) p.uniqueDiffOn_closedExterior).mono inter_subset_left)
  choose B hB using hb
  refine ⟨1 + ∑ i ∈ Finset.range (m + 1), max 0 (B i), ?_, ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ ↦ le_max_left _ _))
  · intro i hi x hx
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (m + 1)) ↦
      le_max_left 0 (B j)) (Finset.mem_range.mpr (show i < m + 1 by omega))
    linarith [hB i x hx, le_max_right 0 (B i)]

/-- A linear rescaling changes each coordinate derivative by at most `2 ^ k`,
the scaling factor in `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem norm_iteratedFDerivWithin_scaledCollarCoordinates_le (k i : ℕ) {x : E}
    (hx : p.radius ≤ ‖x - p.center‖) :
    ‖iteratedFDerivWithin ℝ i (p.scaledCollarCoordinates k)
      {y | p.radius ≤ ‖y - p.center‖} x‖ ≤
    (2 : ℝ) ^ k * ‖iteratedFDerivWithin ℝ i p.collarCoordinates
      {y | p.radius ≤ ‖y - p.center‖} x‖ := by
  let L : (ℝ × E) →L[ℝ] (ℝ × E) :=
    ((2 : ℝ) ^ k • ContinuousLinearMap.fst ℝ ℝ E).prod (ContinuousLinearMap.snd ℝ ℝ E)
  have hL : ‖L‖ ≤ (2 : ℝ) ^ k := by
    apply L.opNorm_le_bound (by positivity)
    intro z
    change max ‖(2 : ℝ) ^ k * z.1‖ ‖z.2‖ ≤ (2 : ℝ) ^ k * ‖z‖
    apply max_le
    · rw [norm_mul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    · exact (le_max_right ‖z.1‖ ‖z.2‖).trans
        (le_mul_of_one_le_left (norm_nonneg z) (one_le_pow₀ (by norm_num)))
  exact (L.norm_iteratedFDerivWithin_comp_left (p.contDiffOn_collarCoordinates x hx)
    p.uniqueDiffOn_closedExterior hx (by simp)).trans
    (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

/-- The derivative bounds needed by the quantitative chain rule for
`app:ch_regular_base:eq:extension-collar-l2`, uniform over the summand index. -/
theorem exists_scaledCollarCoordinates_derivative_bound [FiniteDimensional ℝ E] (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k i : ℕ, 1 ≤ i → i ≤ m → ∀ x ∈ p.compactExteriorCollar,
      ‖iteratedFDerivWithin ℝ i (p.scaledCollarCoordinates k)
        {y | p.radius ≤ ‖y - p.center‖} x‖ ≤ ((2 : ℝ) ^ k * B) ^ i := by
  obtain ⟨B, hB, hb⟩ := p.exists_collarCoordinates_derivative_bound m
  refine ⟨B, hB, ?_⟩
  intro k i hi him x hx
  have hbase : 1 ≤ (2 : ℝ) ^ k * B :=
    hB.trans (le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num)))
  calc
    _ ≤ (2 : ℝ) ^ k * ‖iteratedFDerivWithin ℝ i p.collarCoordinates
        {y | p.radius ≤ ‖y - p.center‖} x‖ :=
      p.norm_iteratedFDerivWithin_scaledCollarCoordinates_le k i hx.1
    _ ≤ (2 : ℝ) ^ k * B := mul_le_mul_of_nonneg_left (hb i him x hx) (by positivity)
    _ ≤ ((2 : ℝ) ^ k * B) ^ i := le_self_pow₀ hbase (by omega)

end JanetCartan.BallExtension.Parameters
