module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Geometry.Locality
public import Mathlib.Analysis.Normed.Ring.Units
/-!
# Uniform mixed bounds for the elapsed phase

Spatial near-identity control gives a uniform determinant gap. Bounding the
temporal mixed row additionally gives a uniform Frobenius inverse bound for
the triangular spacetime matrix. The constants precede the phase and elapsed
time interval. They are the mixed-geometry inputs of the supported integer
Sobolev theorem for `app:ch_regular_base:lem:retarded-kernel`.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
@[expose] public noncomputable section
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open FourierIntegral
variable {d : ℕ}

private theorem matrix_isUnit_of_half_gap (A : Matrix (Fin d) (Fin d) ℝ)
    (h : ‖A - 1‖ ≤ 1 / 2) : IsUnit A.det := by
  have hg : ‖1 - A‖ < 1 := by rw [norm_sub_rev]; linarith
  have hu : IsUnit A := by
    simpa only [Units.val_oneSub, sub_sub_cancel] using (Units.oneSub (1 - A) hg).isUnit
  exact (Matrix.isUnit_iff_isUnit_det A).mp hu

/-- A fixed spatial near-identity ball has a positive determinant gap and
a uniform inverse bound. Consumer: the triangular mixed bounds in the
retarded-kernel fixed-time representation. -/
theorem exists_spatialMixed_half_gap_constants (d : ℕ) :
    ∃ δ > 0, ∃ B > 0, ∀ A : Matrix (Fin d) (Fin d) ℝ,
      ‖A - 1‖ ≤ 1 / 2 → IsUnit A.det ∧ δ ≤ |A.det| ∧ ‖A⁻¹‖ ≤ B := by
  let K := Metric.closedBall (1 : Matrix (Fin d) (Fin d) ℝ) (1 / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hne : K.Nonempty := ⟨1, Metric.mem_closedBall_self (by norm_num)⟩
  have hu : ∀ A ∈ K, IsUnit A.det := fun A hA ↦
    matrix_isUnit_of_half_gap A (by simpa only [K, Metric.mem_closedBall, dist_eq_norm] using hA)
  have hc : ContinuousOn (fun A : Matrix (Fin d) (Fin d) ℝ ↦ |A.det|) K :=
    continuous_id.matrix_det.abs.continuousOn
  obtain ⟨A₀, hA₀, hmin⟩ := hK.exists_isMinOn hne hc
  have hi : ContinuousOn (fun A : Matrix (Fin d) (Fin d) ℝ ↦ ‖A⁻¹‖) K := by
    intro A hA
    exact (continuousAt_matrix_inv A (by
      simpa only [Ring.inverse_eq_inv'] using
        continuousAt_inv₀ (hu A hA).ne_zero)).norm.continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hi
  refine ⟨|A₀.det|, abs_pos.mpr (hu A₀ hA₀).ne_zero, |B| + 1, by positivity, ?_⟩
  intro A hA
  have hm : A ∈ K := by simpa only [K, Metric.mem_closedBall, dist_eq_norm] using hA
  refine ⟨hu A hm, hmin hm, ?_⟩
  have hb := hB A hm
  simpa only [norm_norm] using hb.trans (le_trans (le_abs_self B) (by linarith : |B| ≤ |B| + 1))

private def triangularMatrix (b : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j ↦ Fin.cases (Fin.cases 1 b j) (fun i ↦ Fin.cases 0 (A i) j) i

private theorem det_triangularMatrix (b : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    (triangularMatrix b A).det = A.det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [triangularMatrix, Matrix.submatrix]
  rfl

private theorem continuous_triangularMatrix :
    Continuous (fun p : (Fin d → ℝ) × Matrix (Fin d) (Fin d) ℝ ↦ triangularMatrix p.1 p.2) := by
  apply continuous_matrix
  intro i j
  induction i using Fin.cases with
  | zero =>
      induction j using Fin.cases with
      | zero => exact continuous_const
      | succ j => exact (continuous_apply j).comp continuous_fst
  | succ i =>
      induction j using Fin.cases with
      | zero => exact continuous_const
      | succ j => exact continuous_snd.matrix_elem i j

private theorem exists_elapsedMixed_half_gap_constants (d : ℕ) (L : ℝ) :
    ∃ δ > 0, ∃ B > 0, ∀ (b : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ),
      ‖b‖ ≤ L → ‖A - 1‖ ≤ 1 / 2 →
      IsUnit (triangularMatrix b A).det ∧ δ ≤ |(triangularMatrix b A).det| ∧
        ‖(triangularMatrix b A)⁻¹‖ ≤ B := by
  obtain ⟨δ, hδ, _, _, hδA⟩ := exists_spatialMixed_half_gap_constants d
  let K := Metric.closedBall (0 : Fin d → ℝ) |L| ×ˢ
    Metric.closedBall (1 : Matrix (Fin d) (Fin d) ℝ) (1 / 2)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hu : ∀ p ∈ K, IsUnit (triangularMatrix p.1 p.2).det := by
    intro p hp
    rw [det_triangularMatrix]
    exact (hδA p.2 (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hp.2)).1
  have hi : ContinuousOn (fun p : (Fin d → ℝ) × Matrix (Fin d) (Fin d) ℝ ↦
      ‖(triangularMatrix p.1 p.2)⁻¹‖) K := by
    intro p hp
    have hinv := continuousAt_matrix_inv (triangularMatrix p.1 p.2)
      (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (hu p hp).ne_zero)
    exact (hinv.comp
      (f := fun p : (Fin d → ℝ) × Matrix (Fin d) (Fin d) ℝ ↦ triangularMatrix p.1 p.2)
      continuous_triangularMatrix.continuousAt).norm.continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hi
  refine ⟨δ, hδ, |B| + 1, by positivity, ?_⟩
  intro b A hb hA
  have hm : (b, A) ∈ K := by
    exact ⟨by simpa using hb.trans (le_abs_self L),
      by simpa only [Metric.mem_closedBall, dist_eq_norm] using hA⟩
  refine ⟨hu _ hm, ?_, ?_⟩
  · rw [det_triangularMatrix]
    exact (hδA A hA).2.1
  · have hb' := hB (b, A) hm
    simpa only [norm_norm] using hb'.trans
      (le_trans (le_abs_self B) (by linarith : |B| ≤ |B| + 1))

/-- Uniform mixed invertibility, determinant gap and Frobenius inverse
bounds for every `r ∈ [0, Δ]`, derived from primitive spatial near-identity
control and a temporal mixed-row bound. No smallness of the temporal row
is required. The row bound is a second phase jet whose producer is SymbolBudgets;
spatial near-identity alone cannot bound the inverse temporal shear.
Consumer: the chart inverse bound in `SupportedSobolev.IntegerBounds`,
for `app:ch_regular_base:lem:retarded-kernel`. -/
theorem exists_elapsedPhase_mixed_bounds (d : ℕ) (L : ℝ) :
    ∃ δ > 0, ∃ B > 0, ∀ (Ψ : TwoTimePhase d) (Δ : ℝ)
      (X : Set (Euclidean (d + 1))) (D : Set (Euclidean d)), IsOpen D →
      (∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ η ∈ D, ContDiffAt ℝ ∞
        (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
        ((x 0, x 0 - r), (spatialPart x, η))) →
      (∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ η ∈ D,
        ‖mixedPhaseMatrix (Ψ (x 0) (x 0 - r)) (spatialPart x) η - 1‖ ≤ 1 / 2) →
      (∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ η ∈ D,
        ‖fun j : Fin d ↦ partialDeriv (elapsedTimeDerivative Ψ r (x 0, spatialPart x)) η j‖ ≤ L) →
      ∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ ξ : Euclidean (d + 1), spatialPart ξ ∈ D →
        IsUnit (mixedPhaseMatrix (elapsedPhase Ψ r) x ξ).det ∧
        δ ≤ |(mixedPhaseMatrix (elapsedPhase Ψ r) x ξ).det| ∧
        ‖(mixedPhaseMatrix (elapsedPhase Ψ r) x ξ)⁻¹‖ ≤ B := by
  obtain ⟨δ, hδ, B, hB, hb⟩ := exists_elapsedMixed_half_gap_constants d L
  refine ⟨δ, hδ, B, hB, ?_⟩
  intro Ψ Δ X D hD hs hnear htime r hr x hx ξ hξ
  have hm := mixedPhaseMatrix_elapsedPhase_of_contDiff Ψ r x ξ hD hξ
    (fun η hη ↦ contDiffAt_elapsedSpatialPhase Ψ r (hs r hr x hx η hη))
  have he : mixedPhaseMatrix (elapsedPhase Ψ r) x ξ =
      triangularMatrix (fun j ↦ partialDeriv (elapsedTimeDerivative Ψ r (x 0, spatialPart x))
        (spatialPart ξ) j)
        (mixedPhaseMatrix (Ψ (x 0) (x 0 - r)) (spatialPart x) (spatialPart ξ)) := hm
  rw [he]
  exact hb _ _ (htime r hr x hx _ hξ) (hnear r hr x hx _ hξ)

/-- The exact supported mixed-invertibility input of the existing integer
Sobolev API follows from primitive spatial near-identity control. Unlike
the inverse-norm estimate, this needs no temporal shear bound.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem elapsedPhase_supportedMixedInvertibility (Ψ : TwoTimePhase d) (r : ℝ)
    {X Y : Set (Euclidean (d + 1))} {D : Set (Euclidean d)} (hD : IsOpen D)
    (hs : ∀ x ∈ X, ∀ η ∈ D, ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0 - r), (spatialPart x, η)))
    (hnear : ∀ x ∈ X, ∀ η ∈ D,
      ‖mixedPhaseMatrix (Ψ (x 0) (x 0 - r)) (spatialPart x) η - 1‖ ≤ 1 / 2) :
    SupportedMixedInvertibility (elapsedPhase Ψ r) ((X ×ˢ Y) ×ˢ (spatialPart ⁻¹' D)) := by
  intro p hp
  rw [det_mixedPhaseMatrix_elapsedPhase Ψ r p.1.1 p.2 hD hp.2
    (fun η hη ↦ contDiffAt_elapsedSpatialPhase Ψ r (hs _ hp.1.1 η hη))]
  exact matrix_isUnit_of_half_gap _ (hnear _ hp.1.1 _ hp.2)
end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
