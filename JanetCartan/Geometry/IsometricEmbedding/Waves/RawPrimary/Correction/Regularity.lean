module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.Algebra
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.Regularity
public import JanetCartan.Analysis.Matrix.InverseBounds

/-!
# Smooth orthogonal inverse and fixed-minor bounds

For `app:ch_waves:eq:primary-algebraic-correction`, the actual coefficient map
is smooth near every characteristic matrix with the selected nonzero minor.
The fixed positive minor gap and upper matrix bound give a compact coefficient
range. All low and one-high constants below depend on that range, not on the
phase frequency or the carrier label. The consumer is `fullCorrectionCovector`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open NullTransport

variable {n : ℕ}

private def entriesToMatrix : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
  { LinearMap.id with cont := continuous_id }

private def matrixToEntries : MetricTensor n →L[ℝ] (Fin n → Fin n → ℝ) :=
  { LinearMap.id with cont := continuous_id }

private theorem contDiff_matrixEntry (i j : Fin n) {m : ℕ∞ω} :
    ContDiff ℝ m (fun H : MetricTensor n ↦ H i j) :=
  (contDiff_apply_apply ℝ i j).comp matrixToEntries.contDiff

/-- The adjugate Gram completion is a polynomial coefficient map, before
restricting to the characteristic set
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem contDiff_orthogonalSymbolCompletion (col : Fin n) {m : ℕ∞ω} :
    ContDiff ℝ m (fun H : MetricTensor n ↦ orthogonalSymbolCompletion H col) := by
  apply entriesToMatrix.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  have hk (a : Fin n) : ContDiff ℝ m (fun H : MetricTensor n ↦ rightNullvector H col a) := by
    apply contDiffOn_univ.mp
    exact contDiffOn_adjugate_entry (fun i j ↦ (contDiff_matrixEntry i j).contDiffOn) a col
  change ContDiff ℝ m (fun H : MetricTensor n ↦
    ∑ a, H a i * H a j + rightNullvector H col i * rightNullvector H col j)
  exact (ContDiff.sum fun a _ ↦ (contDiff_matrixEntry a i).mul
    (contDiff_matrixEntry a j)).add ((hk i).mul (hk j))

private theorem contDiff_matrixTranspose {m : ℕ∞ω} :
    ContDiff ℝ m (fun H : MetricTensor n ↦ H.transpose) := by
  apply entriesToMatrix.contDiff.comp
  exact contDiff_pi.mpr fun i ↦ contDiff_pi.mpr fun j ↦ contDiff_matrixEntry j i

/-- The published inverse coefficient is smooth on an ambient neighborhood
of each fixed-minor characteristic matrix, not just along the characteristic
set (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem contDiffAt_orthogonalSymbolInverse {H : MetricTensor n} {row col : Fin n}
    (hH : H.det = 0) (hm : H.adjugate row col ≠ 0) {m : ℕ∞ω} :
    ContDiffAt ℝ m (fun A : MetricTensor n ↦ orthogonalSymbolInverse A col) H :=
  ((contDiffAt_matrix_inv (orthogonalSymbolCompletion_isUnit hH hm)).comp H
    (contDiff_orthogonalSymbolCompletion col).contDiffAt).mul contDiff_matrixTranspose.contDiffAt

/-- Joint finite-order regularity of the concrete inverse, from the primitive
matrix field alone (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem contDiffOn_orthogonalSymbolInverse {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : E → MetricTensor n} {s : Set E} {m : ℕ∞ω}
    (hH : ContDiffOn ℝ m H s) (row col : Fin n)
    (hchar : ∀ x ∈ s, (H x).det = 0)
    (hminor : ∀ x ∈ s, (H x).adjugate row col ≠ 0) :
    ContDiffOn ℝ m (fun x ↦ orthogonalSymbolInverse (H x) col) s := by
  intro x hx
  exact (contDiffAt_orthogonalSymbolInverse (hchar x hx) (hminor x hx)).comp_contDiffWithinAt
    x (hH x hx)

/-- Compact coefficient range determined only by the fixed minor gap and
matrix upper bound (`app:ch_waves:thm:wkb`). -/
def fixedMinorSymbolSet (row col : Fin n) (δ M : ℝ) : Set (MetricTensor n) :=
  Metric.closedBall 0 M ∩ {H | H.det = 0} ∩ {H | δ ≤ |H.adjugate row col|}

/-- The primitive gap and matrix bound define a compact set, furnishing
uniform constants for `app:ch_waves:eq:WKB-grading`. -/
theorem isCompact_fixedMinorSymbolSet (row col : Fin n) (δ M : ℝ) :
    IsCompact (fixedMinorSymbolSet row col δ M) := by
  have hc : Continuous (fun H : MetricTensor n ↦ H.adjugate row col) :=
    ((continuous_apply col).comp (continuous_apply row)).comp continuous_id.matrix_adjugate
  exact ((isCompact_closedBall (0 : MetricTensor n) M).inter_right
    (isClosed_eq continuous_id.matrix_det continuous_const)).inter_right
      (isClosed_le continuous_const hc.abs)

/-- The defining primitive inequalities are exactly membership in the
coefficient range (`app:ch_waves:thm:wkb`). -/
theorem mem_fixedMinorSymbolSet {H : MetricTensor n} {row col : Fin n} {δ M : ℝ} :
    H ∈ fixedMinorSymbolSet row col δ M ↔
      ‖H‖ ≤ M ∧ H.det = 0 ∧ δ ≤ |H.adjugate row col| := by
  simp only [fixedMinorSymbolSet, mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
    mem_ofPred_eq, and_assoc]

/-- A uniform bound for the concrete inverse and the inverse Gram completion
from the fixed minor gap and upper matrix bound alone
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem exists_orthogonalSymbolInverse_uniform_bound (row col : Fin n)
    {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ H : MetricTensor n,
      H.det = 0 → δ ≤ |H.adjugate row col| → ‖H‖ ≤ M →
      ‖orthogonalSymbolInverse H col‖ ≤ B ∧ ‖(orthogonalSymbolCompletion H col)⁻¹‖ ≤ B := by
  let s := fixedMinorSymbolSet row col δ M
  have hs := isCompact_fixedMinorSymbolSet row col δ M
  have hu (H : MetricTensor n) (hH : H ∈ s) : IsUnit (orthogonalSymbolCompletion H col) :=
    orthogonalSymbolCompletion_isUnit hH.1.2 (abs_pos.mp (hδ.trans_le hH.2))
  have hR : ContinuousOn (fun H ↦ ‖orthogonalSymbolInverse H col‖) s := by
    intro H hH
    exact ((contDiffAt_orthogonalSymbolInverse (m := 0) hH.1.2
      (abs_pos.mp (hδ.trans_le hH.2))).continuousAt.norm).continuousWithinAt
  have hC : ContinuousOn (fun H ↦ ‖(orthogonalSymbolCompletion H col)⁻¹‖) s :=
    (contDiffOn_matrix_inv (contDiff_orthogonalSymbolCompletion col (m := 0)).contDiffOn hu).continuousOn.norm
  obtain ⟨BR, hBR⟩ := hs.bddAbove_image hR
  obtain ⟨BC, hBC⟩ := hs.bddAbove_image hC
  refine ⟨1 + max 0 (max BR BC), by positivity, ?_⟩
  intro H hH hm hM
  have hHs : H ∈ s := mem_fixedMinorSymbolSet.mpr ⟨hM, hH, hm⟩
  constructor
  · exact (hBR (mem_image_of_mem _ hHs)).trans (by grind [le_max_left, le_max_right])
  · exact (hBC (mem_image_of_mem _ hHs)).trans (by grind [le_max_left, le_max_right])

/-- The same primitive bounds give a positive completion determinant gap,
uniform over the whole matrix range (`app:ch_waves:thm:wkb`). -/
theorem exists_orthogonalSymbolCompletion_det_gap (row col : Fin n)
    {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : MetricTensor n,
      H.det = 0 → δ ≤ |H.adjugate row col| → ‖H‖ ≤ M →
      ε ≤ |(orthogonalSymbolCompletion H col).det| := by
  have hc : Continuous (fun H : MetricTensor n ↦ |(orthogonalSymbolCompletion H col).det|) :=
    ((contDiff_orthogonalSymbolCompletion col (m := 0)).continuous.matrix_det).abs
  obtain ⟨ε, hε, hb⟩ := (isCompact_fixedMinorSymbolSet row col δ M).exists_forall_le'
    hc.continuousOn (fun H hH ↦ abs_pos.mpr
      (((orthogonalSymbolCompletion H col).isUnit_iff_isUnit_det.mp
        (orthogonalSymbolCompletion_isUnit hH.1.2 (abs_pos.mp (hδ.trans_le hH.2)))).ne_zero))
  exact ⟨ε, hε, fun H hH hm hM ↦ hb H (mem_fixedMinorSymbolSet.mpr ⟨hM, hH, hm⟩)⟩

/-- A finite-order one-high estimate directly in the primitive matrix jets.
There is no assumption on completion jets, inverse jets, or inverse low norms.
The constant is uniform over all smooth fields with the SAME fixed minor gap
and upper matrix bound (`app:ch_waves:eq:WKB-grading`). -/
theorem exists_cNorm_orthogonalSymbolInverse_le_tame {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) (row col : Fin n)
    {δ : ℝ} (hδ : 0 < δ) (M : ℝ) {r k : ℕ} (hrk : r ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : E → MetricTensor n, ContDiff ℝ ∞ H →
      (∀ y ∈ Metric.closedBall x ρ, (H y).det = 0) →
      (∀ y ∈ Metric.closedBall x ρ, δ ≤ |(H y).adjugate row col|) →
      (∀ y ∈ Metric.closedBall x ρ, ‖H y‖ ≤ M) →
      cNorm (Metric.closedBall x ρ) r (fun y ↦ orthogonalSymbolInverse (H y) col) ≤
        C * (1 + cNorm (Metric.closedBall x ρ) k H) := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_comp_le_tame_closedBall_of_compact_range
    x hρ (isCompact_fixedMinorSymbolSet row col δ M) hrk
    (fun H hH ↦ contDiffAt_orthogonalSymbolInverse (m := r) hH.1.2
      (abs_pos.mp (hδ.trans_le hH.2)))
  refine ⟨C, hC, fun H hH hc hm hM ↦ hb H hH ?_⟩
  intro y hy
  exact mem_fixedMinorSymbolSet.mpr ⟨hM y hy, hc y hy, hm y hy⟩

/-- Primitive matrix grades transfer to the SAME orthogonal inverse, with a
constant chosen before the scale or the field. This is the inverse operation
in `app:ch_waves:eq:WKB-grading`. -/
theorem exists_cNorm_orthogonalSymbolInverse_le_graded {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) (row col : Fin n)
    {δ : ℝ} (hδ : 0 < δ) (M : ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L D : ℝ), 1 ≤ L → 0 ≤ D →
      ∀ H : E → MetricTensor n, ContDiff ℝ ∞ H →
      (∀ y ∈ Metric.closedBall x ρ, (H y).det = 0) →
      (∀ y ∈ Metric.closedBall x ρ, δ ≤ |(H y).adjugate row col|) →
      (∀ y ∈ Metric.closedBall x ρ, ‖H y‖ ≤ M) →
      cNorm (Metric.closedBall x ρ) r H ≤ D * L ^ r →
      cNorm (Metric.closedBall x ρ) r (fun y ↦ orthogonalSymbolInverse (H y) col) ≤
        C * (1 + D) * L ^ r := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_orthogonalSymbolInverse_le_tame
    x hρ row col hδ M (r := r) le_rfl
  refine ⟨C, hC, fun L D hL _ H hH hc hm hM hbudget ↦ ?_⟩
  apply (hb H hH hc hm hM).trans
  have hpow : 1 ≤ L ^ r := one_le_pow₀ hL
  nlinarith

end JanetCartan.RawPrimary
