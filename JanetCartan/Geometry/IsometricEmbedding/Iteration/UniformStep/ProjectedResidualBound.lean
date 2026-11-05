module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.HistoryGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmbientStrain.FrameBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.AngularConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.ScaledReference

/-!
# A fixed reconstruction constant for the actual projected stress row

The reduced residual in `app:ch_pairs:eq:pairs-lag-sum-error` is reconstructed
using the same projected stress row and its inverse Gram matrix. The existing
raw-primary frame threshold gives an explicit constant before the current
map is chosen. The finite-history theorem supplies its hypotheses for the
same fixed reference; it does not choose a new source scale or row.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.UniformStep

open ProjectedStressFrame RawPrimary

/-- Fixed full-strain reconstruction constant for
`app:ch_pairs:eq:pairs-lag-sum-error`, using the SAME raw-primary frame
threshold and Gram gap. It precedes accuracy, source scale, target and history. -/
def projectedStressResidualConstant {n : ℕ} (hn : 5 ≤ n) : ℝ :=
  2 * (n : ℝ) ^ 3 * (ambientStrainFrameGramGap hn)⁻¹ *
    (ambientStrainFrameThreshold hn + ‖cubeStress n‖)

/-- Positivity of the fixed inverse-Gram transfer constant in
`app:ch_pairs:eq:pairs-lag-sum-error`. -/
theorem projectedStressResidualConstant_pos {n : ℕ} (hn : 5 ≤ n) :
    0 < projectedStressResidualConstant hn := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hgap := ambientStrainFrameGramGap_pos hn
  have hthreshold := ambientStrainFrameThreshold_pos hn
  unfold projectedStressResidualConstant
  positivity

/-- The `hgram` input of
`cut_sampled_ambient_product_stage_error_le_of_reduced_residual` is a
conclusion of the original frame neighborhood. The row and its matrix inverse
are the literal projected stresses, and no inverse bound is assumed
(`app:ch_pairs:eq:pairs-lag-sum-error`). -/
theorem projectedStress_residual_coefficient_le {n : ℕ} (hn : 5 ≤ n)
    {F : Euclidean n → Euclidean (embeddingDimension n)}
    {U K : Set (Euclidean n)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hclose : ∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) <
      ambientStrainFrameThreshold hn)
    {x : Euclidean n} (hx : x ∈ K) :
    2 * (∑ a, ∑ b, |(stressGram (projectedStress F x))⁻¹ a b| *
      ‖projectedStress F x a‖) ≤ projectedStressResidualConstant hn := by
  have hinv := (projectedStress_inverseGram_bound_of_cNorm_closeness
    hn hU hK hKU hF hi hrank hclose hx).2
  have hdist := ActualCarriers.projectedStress_norm_sub_cube_lt_of_cNorm
    hU hK hKU hF hi hrank (ambientStrainFrameThreshold_pos hn) hclose hx
  have hrow : ‖projectedStress F x‖ ≤ ambientStrainFrameThreshold hn + ‖cubeStress n‖ :=
    (norm_le_norm_sub_add (projectedStress F x) (cubeStress n)).trans
      (add_le_add hdist.le le_rfl)
  have hentry (a b : Fin n) : |(stressGram (projectedStress F x))⁻¹ a b| ≤
      n * (ambientStrainFrameGramGap hn)⁻¹ :=
    (ActualCarriers.abs_entry_le_frobenius _ a b).trans hinv
  have hrowentry (a : Fin n) : ‖projectedStress F x a‖ ≤
      ambientStrainFrameThreshold hn + ‖cubeStress n‖ :=
    (norm_le_pi_norm _ a).trans hrow
  have hgap := ambientStrainFrameGramGap_pos hn
  calc
    _ ≤ 2 * (∑ _a : Fin n, ∑ _b : Fin n,
        (n * (ambientStrainFrameGramGap hn)⁻¹) *
          (ambientStrainFrameThreshold hn + ‖cubeStress n‖)) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦
          mul_le_mul (hentry a b) (hrowentry a) (norm_nonneg _) (by positivity))
        (by norm_num)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        projectedStressResidualConstant]
      ring

/-- `main:eq:displacement-budget` supplies the fixed row and reconstruction
bound for every admissible history, using the SAME initialized reference.
The reference tolerance is an existing output of the full-margin initializer
with the raw-primary frame threshold. The larger carrier domain remains that
of the original analytic source `G₀`, even when `G` has a smaller working
chart. The initial-frequency threshold is chosen before all histories and
does not depend on accuracy or target dilation.
This discharges the geometric reconstruction input in
`cut_sampled_ambient_product_stage_error_le_of_reduced_residual`. -/
theorem exists_initialScale_for_projected_residual_bound {n : ℕ} (hn : 5 ≤ n)
    (G₀ G : FlatReference n) {ρ r R : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hmap : G.map = sourceDilation G₀.map ρ) (hr : 0 < r) (hrR : r < R)
    (hR : R < G₀.domain.chartRadius) {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin)
    (hreference : ∀ i, cNorm (closedBall (0 : Euclidean n) r) 6
      (fun x ↦ projectedStress G.map x i - cubeStress n i) <
        ambientStrainFrameThreshold hn / 2) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ R₀, T ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
      ∀ x ∈ closedBall (0 : Euclidean n) r,
        LinearIndependent ℝ (projectedStress F x) ∧
        (Submodule.span ℝ (range (projectedStress F x)) : Set (MetricTensor n)) =
          stressSpace F x ∧
        2 * (∑ a, ∑ b, |(stressGram (projectedStress F x))⁻¹ a b| *
          ‖projectedStress F x a‖) ≤ projectedStressResidualConstant hn := by
  let H := sourceDilationReference G₀ hρ hρ₁
  have hsame : G.map = H.map := hmap
  have href : ∀ i, cNorm (closedBall (0 : Euclidean n) r) 6
      (fun x ↦ projectedStress H.map x i - cubeStress n i) <
        ambientStrainFrameThreshold hn / 2 := by
    rw [← hsame]
    exact hreference
  obtain ⟨T, hT, _, _, _, _, hhistory⟩ := HistoryGeometry.exists_cube_frame_neighborhood
    H hr hrR hR horder (ambientStrainFrameThreshold_pos hn) href
  rw [← hsame] at hhistory
  refine ⟨T, hT, ?_⟩
  intro R₀ hR₀ j u ell hu
  obtain ⟨hi, hrank, _, _, _, _, hclose⟩ := hhistory R₀ hR₀ j u ell hu
  have hF := (hu.contDiff_finiteHistoryMap G.contDiff).contDiffOn (s := ball 0 R)
  have hKU : closedBall (0 : Euclidean n) r ⊆ ball 0 R := closedBall_subset_ball hrR
  refine ⟨hi, hrank, ?_⟩
  intro x hx
  have hframe := projectedStress_tensorFrame_of_cNorm_closeness hn isOpen_ball
    (isCompact_closedBall _ _) hKU hF hi hrank hclose hx
  exact ⟨hframe.2.1, hframe.2.2, projectedStress_residual_coefficient_le hn isOpen_ball
    (isCompact_closedBall _ _) hKU hF hi hrank hclose hx⟩

end JanetCartan.UniformStep
