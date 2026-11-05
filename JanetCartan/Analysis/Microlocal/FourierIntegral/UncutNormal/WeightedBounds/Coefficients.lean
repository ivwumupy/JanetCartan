module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.WeightedDiagonal
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Bounds
public import JanetCartan.Analysis.Matrix.InverseBounds.Algebra

/-!
# Fixed coefficient estimates for the weighted graph

The inverse and absolute determinant in
`app:ch_regular_base:eq:actual-matrix-inverse` are estimated from the original
matrix norm and determinant gaps. Constants precede the fields, chart and shell.
The consumer is the normalized weighted-amplitude estimate for
`WholeImageGeometry.exists_graphL2_of_wholeImage_phase`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.UncutNormal
open NormalComparison
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Smooth complex matrix inversion at a primitive determinant gap, for
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem complexMatrixInverse_contDiffAt {U : Mat} (hU : U.det ≠ 0) :
    ContDiffAt ℝ ∞ (fun V : Mat ↦ V⁻¹) U := by
  rcases (Matrix.isUnit_iff_isUnit_det U).mpr (isUnit_iff_ne_zero.mpr hU) with ⟨u, rfl⟩
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using (contDiffAt_ringInverse ℝ u)

private theorem exists_compact_coefficient_jet_bound
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (N : ℕ) {K : Set F} (hK : IsCompact K) {f : F → G}
    (hf : ∀ p ∈ K, ContDiffAt ℝ ∞ f p) :
    ∃ C > 0, ∀ p ∈ K, ∀ k ≤ N, ‖iteratedFDeriv ℝ k f p‖ ≤ C := by
  have hb (k : ℕ) : ∃ C : ℝ, ∀ p ∈ K, ‖iteratedFDeriv ℝ k f p‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    intro p hp
    exact ((hf p hp).continuousAt_iteratedFDeriv (by simp)).continuousWithinAt
  choose C hC using hb
  refine ⟨1 + ∑ k ∈ Finset.range (N + 1), |C k|, by positivity, ?_⟩
  intro p hp k hk
  have hs := Finset.single_le_sum (fun i _ ↦ abs_nonneg (C i))
    (Finset.mem_range.mpr (by omega : k < N + 1))
  have h := hC k p hp
  linarith [le_abs_self (C k)]

/-- The inverse coefficient jets, including its norm, follow from an original
matrix bound and a positive determinant gap. No inverse norm is assumed.
Source: `app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem exists_complexMatrixInverse_jet_bound (N : ℕ) (M : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ U : Mat, ‖U‖ ≤ M → δ ≤ ‖U.det‖ → ∀ k ≤ N,
      ‖iteratedFDeriv ℝ k (fun V : Mat ↦ V⁻¹) U‖ ≤ C := by
  let K : Set Mat := {U | ‖U‖ ≤ M ∧ δ ≤ ‖U.det‖}
  have hK : IsCompact K := (isCompact_closedBall (0 : Mat) M).of_isClosed_subset
    ((isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const continuous_id.matrix_det.norm))
    (fun _ h ↦ by simpa only [Metric.mem_closedBall, dist_zero_right] using h.1)
  obtain ⟨C, hC, hb⟩ := exists_compact_coefficient_jet_bound N hK
    (fun _ h ↦ complexMatrixInverse_contDiffAt (norm_pos_iff.mp (hδ.trans_le h.2)))
  exact ⟨C, hC, fun U hU hgap ↦ hb U ⟨hU, hgap⟩⟩

/-- Absolute determinant coefficient jets follow from the original differential
norm and its gap. This is the density factor of
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem exists_absNormalDeterminant_jet_bound (N : ℕ) (M : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ J : E →L[ℝ] E, ‖J‖ ≤ M → δ ≤ |J.det| → ∀ k ≤ N,
      ‖iteratedFDeriv ℝ k (fun L : E →L[ℝ] E ↦ |L.det|) J‖ ≤ C := by
  let K : Set (E →L[ℝ] E) := {J | ‖J‖ ≤ M ∧ δ ≤ |J.det|}
  have hK : IsCompact K := (isCompact_closedBall (0 : E →L[ℝ] E) M).of_isClosed_subset
    ((isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const ContinuousLinearMap.continuous_det.abs))
    (fun _ h ↦ by simpa only [Metric.mem_closedBall, dist_zero_right] using h.1)
  obtain ⟨C, hC, hb⟩ := exists_compact_coefficient_jet_bound N hK
    (fun _ h ↦ contDiff_normalJacobianDet.contDiffAt.abs (abs_pos.mp (hδ.trans_le h.2)))
  exact ⟨C, hC, fun J hJ hgap ↦ hb J ⟨hJ, hgap⟩⟩

/-- Original scalar mask, mixed phase differential and transport matrix.
No transformed quantity is included in this coefficient input for
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
abbrev WeightedPrimitiveCoefficients (n r : ℕ) :=
  ℝ × ((Euclidean n →L[ℝ] Euclidean n) × Matrix (Fin r) (Fin r) ℂ)

/-- The fixed coefficient operation `c |det J| U⁻*`, retaining the complete
real mask, in `app:ch_regular_base:eq:actual-matrix-inverse`. -/
def weightedPrimitiveCoefficient (p : WeightedPrimitiveCoefficients n r) : Mat :=
  (p.1 : ℂ) • weightedForwardAmplitude |p.2.1.det| p.2.2

/-- The coefficient operation is smooth exactly where its two original
matrices are nonsingular, for `app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem weightedPrimitiveCoefficient_contDiffAt {p : WeightedPrimitiveCoefficients n r}
    (hJ : p.2.1.det ≠ 0) (hU : p.2.2.det ≠ 0) :
    ContDiffAt ℝ ∞ weightedPrimitiveCoefficient p := by
  have hstar : ContDiff ℝ ∞ (fun U : Mat ↦ U.conjTranspose) :=
    (Matrix.conjTransposeLinearEquiv (Fin r) (Fin r) ℝ ℂ).toContinuousLinearEquiv.contDiff
  have hmask : ContDiffAt ℝ ∞ (fun q : WeightedPrimitiveCoefficients n r ↦ (q.1 : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p contDiffAt_fst
  have hdet := (contDiff_normalJacobianDet.contDiffAt.abs hJ).comp p
    (contDiffAt_snd.fst : ContDiffAt ℝ ∞ (fun q : WeightedPrimitiveCoefficients n r ↦ q.2.1) p)
  exact hmask.smul (hstar.contDiffAt.comp p
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp p hdet).smul
      ((complexMatrixInverse_contDiffAt hU).comp p contDiffAt_snd.snd)))

/-- Finite jets of the weighted coefficient, on a set fixed before all fields
and dyadic indices. The only size and gap inputs are primitive values.
Source: `app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem exists_weightedPrimitiveCoefficient_jet_bound (N : ℕ) (M : ℝ)
    {δJ δU : ℝ} (hδJ : 0 < δJ) (hδU : 0 < δU) :
    ∃ C > 0, ∀ p : WeightedPrimitiveCoefficients n r,
      ‖p‖ ≤ M → δJ ≤ |p.2.1.det| → δU ≤ ‖p.2.2.det‖ → ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k weightedPrimitiveCoefficient p‖ ≤ C := by
  let K : Set (WeightedPrimitiveCoefficients n r) :=
    {p | ‖p‖ ≤ M ∧ δJ ≤ |p.2.1.det| ∧ δU ≤ ‖p.2.2.det‖}
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : WeightedPrimitiveCoefficients n r) M).of_isClosed_subset
      ((isClosed_le continuous_norm continuous_const).inter
        ((isClosed_le continuous_const
          (ContinuousLinearMap.continuous_det.comp continuous_snd.fst).abs).inter
          (isClosed_le continuous_const continuous_snd.snd.matrix_det.norm)))
      (fun _ h ↦ by simpa only [Metric.mem_closedBall, dist_zero_right] using h.1)
  obtain ⟨C, hC, hb⟩ := exists_compact_coefficient_jet_bound N hK
    (fun _ h ↦ weightedPrimitiveCoefficient_contDiffAt
      (abs_pos.mp (hδJ.trans_le h.2.1)) (norm_pos_iff.mp (hδU.trans_le h.2.2)))
  exact ⟨C, hC, fun p hp hJ hU ↦ hb p ⟨hp, hJ, hU⟩⟩

end JanetCartan.FourierIntegral.UncutNormal
