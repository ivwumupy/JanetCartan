module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Linearity.Span
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PreparationTransportPrimitives.InitialCoordinates

/-!
# Smooth preparation scalars in the original admitted span

The corrected-atom maps act on `initialScalarSpan`, whereas finite preparation
uses smooth scalars without a size constraint on their linear domain. A fixed
strict margin in the original positive class makes every smooth scalar a
linear combination of two members of that same class. The initial compact,
radius and class are not changed. This supplies the domain connection for
the literal preparation current map and its homogeneous atom estimates.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff

namespace JanetCartan.CurrentMean
open PrimarySourceAdmission ContinuumRow PreparationTransportPrimitives

/-- The constant center of the original positive scalar class has no higher
jets (`app:ch_response:cor:current-atoms`). -/
private theorem cNorm_preparationConstant_le {n : ℕ}
    (I : Set (Euclidean (n - 1) × Euclidean 3)) (s : ℕ) (b : ℝ) :
    cNorm I s (fun _ ↦ b) ≤ |b| := by
  induction s with
  | zero =>
    rw [cNorm_order_zero]
    exact Real.sSup_le (by rintro _ ⟨_, _, rfl⟩; exact le_rfl) (abs_nonneg b)
  | succ s ih =>
    rw [cNorm_succ]
    have hz : sSup ((fun x : Euclidean (n - 1) × Euclidean 3 ↦
        ‖iteratedFDeriv ℝ (s + 1) (fun _ : Euclidean (n - 1) × Euclidean 3 ↦ b) x‖) '' I) ≤ 0 := by
      apply Real.sSup_le _ le_rfl
      rintro _ ⟨x, _, rfl⟩
      simp [iteratedFDeriv_succ_const]
    linarith

/-- Every smooth scalar belongs to the span of the SAME original positive
class when its prescribed lower and upper bounds have a strict margin.
Normalize by the actual order-fourteen seminorm on the unchanged initial
compact. This closes the domain mismatch between preparation and the
corrected-atom linear maps (`app:ch_mean_pairs:eq:mean-density-lipschitz`,
`app:ch_response:cor:current-atoms`). -/
theorem mem_initialScalarSpan_of_contDiff {n : ℕ} (z₀ : Euclidean 3) (R : ℝ)
    {M m : ℝ} (hm : 0 ≤ m) (hgap : m < M)
    {u : Euclidean (n - 1) × Euclidean 3 → ℝ} (hu : ContDiff ℝ ∞ u) :
    u ∈ initialScalarSpan z₀ R M m := by
  let I := closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)
  let b := (M + m) / 2
  let δ := (M - m) / 2
  let p := cNorm I 14 u
  let t := δ / (p + 1)
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hp : 0 ≤ p := cNorm_nonneg _ _ _
  have ht : 0 < t := div_pos hδ (by linarith)
  have htp : t * p ≤ δ := by
    have hh := mul_le_mul_of_nonneg_left (show p ≤ p + 1 by linarith) ht.le
    simpa only [t, div_mul_cancel₀ _ (show p + 1 ≠ 0 by linarith)] using hh
  have hbase : (fun _ : Euclidean (n - 1) × Euclidean 3 ↦ b) ∈
      primitiveInitialScalars z₀ R M m := by
    refine ⟨contDiffOn_const, ?_, ?_⟩
    · apply (cNorm_preparationConstant_le I 14 b).trans
      rw [abs_of_nonneg hb]
      dsimp [b]
      linarith
    · intro x _
      dsimp [b]
      linarith
  let v := (fun _ : Euclidean (n - 1) × Euclidean 3 ↦ b) + t • u
  have hv : v ∈ primitiveInitialScalars z₀ R M m := by
    refine ⟨(contDiff_const.add (hu.const_smul t)).contDiffOn, ?_, ?_⟩
    · apply (cNorm_add_le (isCompact_closedBall _ _) contDiff_const
        ((hu.of_le (by simp : (14 : ℕ∞ω) ≤ ∞)).const_smul t)).trans
      change cNorm I 14 (fun _ ↦ b) + cNorm I 14 (t • u) ≤ M
      rw [cNorm_smul t (hu.of_le (by simp)), Real.norm_eq_abs, abs_of_pos ht]
      have hbc := cNorm_preparationConstant_le I 14 b
      rw [abs_of_nonneg hb] at hbc
      change _ + t * p ≤ M
      dsimp [b, δ] at hbc htp
      linarith
    · intro x hx
      have huabs : |u x| ≤ p := by
        simpa only [Real.norm_eq_abs] using norm_le_cNorm (isCompact_closedBall _ _)
          (hu.of_le (by simp : (14 : ℕ∞ω) ≤ ∞)) (ball_subset_closedBall hx)
      have htu := mul_le_mul_of_nonneg_left (abs_le.mp huabs).1 ht.le
      change m ≤ b + t * u x
      dsimp [b, δ] at *
      nlinarith
  have hdiff : t • u ∈ initialScalarSpan z₀ R M m := by
    have hh := (initialScalarSpan z₀ R M m).sub_mem (Submodule.subset_span hv)
      (Submodule.subset_span hbase)
    simpa only [v, add_sub_cancel_left] using hh
  have hh := (initialScalarSpan z₀ R M m).smul_mem t⁻¹ hdiff
  simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using hh

/-- Every original smooth preparation scalar is admitted by the corrected
linear family after the existing fixed coordinate relabeling. No new scalar
or initial compact is chosen (`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem preparationCharacteristicInitial_mem_span {n : ℕ}
    (z₀ : Euclidean 3) (R : ℝ) {M m : ℝ} (hm : 0 ≤ m) (hgap : m < M)
    {u : CarrierVariable n → ℝ} (hu : ContDiff ℝ ∞ u) :
    preparationCharacteristicInitial u ∈ initialScalarSpan z₀ R M m :=
  mem_initialScalarSpan_of_contDiff z₀ R hm hgap (preparationCharacteristicInitial_contDiff hu)

end JanetCartan.CurrentMean
