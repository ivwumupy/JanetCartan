module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.Coefficients
public import JanetCartan.Analysis.Microlocal.FourierIntegral.Kernel
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.MatrixKernels

/-!
# Source coefficients of full matrix graph amplitudes

The pointwise matrix reconstruction and Frobenius coefficient estimates for
`app:ch_regular_base:thm:actual-calculus`, Step 1. The coefficients retain the
output and physical covector variables. Only the source variable is expanded.
These statements do not yet commute output/covector derivatives with integration
or exchange the source series with the oscillatory kernel integrals.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.SourceExpansion

open AmplitudeBound

variable {n r : ℕ}

/-- Source-independent matrix coefficients of the actual full amplitude in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def matrixCoefficient (ℓ : ℝ) (A : FullAmplitude n r) (k : Fin n → ℤ)
    (x η : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  fun i j ↦ scalarCoefficient ℓ (fun y ↦ A x y η i j) k

/-- A common zero source fiber is retained by every source coefficient,
so the expansion does not enlarge output/covector supports
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem matrixCoefficient_eq_zero_of_fiber (ℓ : ℝ) (A : FullAmplitude n r)
    (k : Fin n → ℤ) (x η : Euclidean n) (h : ∀ y, A x y η = 0) :
    matrixCoefficient ℓ A k x η = 0 := by
  ext i j
  simp [matrixCoefficient, h]

/-- The coefficients of the literal compact-frequency regularization are
the same cutoff times the coefficients of the full amplitude. This also holds
for any scalar output/covector cutoff
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem matrixCoefficient_external_smul (ℓ : ℝ) (A : FullAmplitude n r)
    (χ : Euclidean n → Euclidean n → ℂ) (k : Fin n → ℤ) (x η : Euclidean n) :
    matrixCoefficient ℓ (fun x y η ↦ χ x η • A x y η) k x η =
      χ x η • matrixCoefficient ℓ A k x η := by
  ext i j
  exact scalarCoefficient_const_mul ℓ (fun y ↦ A x y η i j) (χ x η) k

private theorem frobenius_norm_le_sum (M : Matrix (Fin r) (Fin r) ℂ) :
    ‖M‖ ≤ ∑ i, ∑ j, ‖M i j‖ := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp_rw [Real.rpow_two]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ ∑ i, (∑ j, ‖M i j‖) ^ 2 := Finset.sum_le_sum fun i _ ↦
      Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)
    _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ by positivity)

/-- Frobenius source-derivative bounds imply decay of each actual coefficient
entry (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem norm_matrixCoefficient_entry_le (hn : 0 < n) {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hf : ∀ x η, ContDiff ℝ ∞ (fun y ↦ A x y η))
    (N : ℕ) {B : ℝ} (hzero : ∀ x η y, ‖A x y η‖ ≤ B)
    (hderiv : ∀ x η i y,
      ‖matrixAmplitudeCoordinateDerivList (List.replicate N i) (fun y ↦ A x y η) y‖ ≤ B)
    (k : Fin n → ℤ) (x η : Euclidean n) (i j : Fin r) :
    ‖matrixCoefficient ℓ A k x η i j‖ ≤
      coefficientConstant n N ℓ * B * decayWeight N k := by
  apply norm_scalarCoefficient_le hn hℓ hR (hs x η i j)
    ((matrixEntryEvaluation i j).contDiff.comp (hf x η)) N
  · intro y
    exact (norm_matrixEntry_le_frobenius _ i j).trans (hzero x η y)
  · intro a y
    exact (norm_matrixEntry_le_frobenius _ i j).trans (hderiv x η a y)

/-- Actual source coefficients decay in Frobenius norm, uniformly in both
remaining physical variables (`app:ch_regular_base:thm:actual-calculus`, Step 1).
The dimension factor is harmless because matrix size is fixed. -/
theorem norm_matrixCoefficient_le (hn : 0 < n) {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hf : ∀ x η, ContDiff ℝ ∞ (fun y ↦ A x y η))
    (N : ℕ) {B : ℝ} (hzero : ∀ x η y, ‖A x y η‖ ≤ B)
    (hderiv : ∀ x η i y,
      ‖matrixAmplitudeCoordinateDerivList (List.replicate N i) (fun y ↦ A x y η) y‖ ≤ B)
    (k : Fin n → ℤ) (x η : Euclidean n) :
    ‖matrixCoefficient ℓ A k x η‖ ≤
      (r : ℝ) ^ 2 * coefficientConstant n N ℓ * B * decayWeight N k := by
  calc
    _ ≤ ∑ i, ∑ j, ‖matrixCoefficient ℓ A k x η i j‖ := frobenius_norm_le_sum _
    _ ≤ ∑ _i : Fin r, ∑ _j : Fin r, coefficientConstant n N ℓ * B * decayWeight N k :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        norm_matrixCoefficient_entry_le hn hℓ hR A hs hf N hzero hderiv k x η i j
    _ = _ := by simp; ring

/-- The full matrix amplitude is recovered on the original Euclidean source
space with one common cutoff. All original supports are retained by the exact
equality (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem hasSum_matrixCoefficient_cutoff (hn : 0 < n) {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hf : ∀ x η, ContDiff ℝ ∞ (fun y ↦ A x y η))
    {B : ℝ} (hzero : ∀ x η y, ‖A x y η‖ ≤ B)
    (hderiv : ∀ x η i y,
      ‖matrixAmplitudeCoordinateDerivList (List.replicate (lowReserve n) i)
        (fun y ↦ A x y η) y‖ ≤ B)
    (β : Euclidean n → ℂ)
    (hβcell : ∀ y, β y ≠ 0 → ℓ⁻¹ • y ∈ fundamentalCell n)
    (hβone : ∀ x η y, A x y η ≠ 0 → β y = 1) (x y η : Euclidean n) :
    HasSum (fun k ↦ (β y * sourceMode ℓ k y) • matrixCoefficient ℓ A k x η)
      (A x y η) := by
  apply Pi.hasSum.mpr
  intro i
  apply Pi.hasSum.mpr
  intro j
  have hz (y) : ‖A x y η i j‖ ≤ B :=
    (norm_matrixEntry_le_frobenius _ i j).trans (hzero x η y)
  have hd (a y) :
      ‖euclideanCoordinateDerivList (List.replicate (lowReserve n) a)
        (fun y ↦ A x y η i j) y‖ ≤ B :=
    (norm_matrixEntry_le_frobenius _ i j).trans (hderiv x η a y)
  have hb (y) (hy : A x y η i j ≠ 0) : β y = 1 := by
    apply hβone x η y
    intro h
    exact hy (congrArg (fun M : Matrix (Fin r) (Fin r) ℂ ↦ M i j) h)
  simpa only [Matrix.smul_apply, smul_eq_mul, matrixCoefficient, mul_comm] using
    hasSum_scalarCoefficient_cutoff hn hℓ hR (hs x η i j)
      ((matrixEntryEvaluation i j).contDiff.comp (hf x η)) hz hd β hβcell hb y

end JanetCartan.FourierIntegral.SourceExpansion
