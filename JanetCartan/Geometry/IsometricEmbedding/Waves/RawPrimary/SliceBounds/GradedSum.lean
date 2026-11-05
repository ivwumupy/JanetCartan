module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DyadicSum
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.Branches

/-!
# Graded dyadic summation on the original Hilbert input

The last summation in `app:ch_waves:eq:individual-raw-slice` retains
`κ^q L^(s-q)` until `L ≤ K` and the actual `4K` ceiling are used. This is an
algebraic deduction from the normalized branch operators; their actual
construction must apply `exists_wideBandSliceOperator` to the primitive
inputs from `exists_rawSlicePrimitiveBranchNormalData`. No analytic production
or Sobolev membership is asserted by this finite-sum lemma.
-/

@[expose] public noncomputable section

namespace JanetCartan.RawPrimary.SliceBounds
open RawInputPartition

variable {n J s : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Sum the exact branch prefactors on the original wide data, after the
normalized slice channels have been constructed
(`app:ch_waves:eq:individual-raw-slice`). -/
def gradedWideBandOperatorSum
    (T : SliceDerivativeBranch s → (j : Fin J) → WideBandL2 n j.val →L[ℂ] E)
    (L : ℝ) : WideInput n J →L[ℂ] E :=
  ∑ b : SliceDerivativeBranch s, wideBandOperatorSum
    (fun j ↦ (((2 : ℝ) ^ j.val) ^ b.phaseCount * L ^ (s - b.phaseCount)) • T b j)

/-- Literal evaluation retains every exact physical grade before estimating
it (`app:ch_waves:eq:individual-raw-slice`). -/
theorem gradedWideBandOperatorSum_apply
    (T : SliceDerivativeBranch s → (j : Fin J) → WideBandL2 n j.val →L[ℂ] E)
    (L : ℝ) (v : WideInput n J) :
    gradedWideBandOperatorSum T L v =
      ∑ b : SliceDerivativeBranch s, ∑ j : Fin J,
        (((2 : ℝ) ^ j.val) ^ b.phaseCount * L ^ (s - b.phaseCount)) • T b j (v j) := by
  simp [gradedWideBandOperatorSum, wideBandOperatorSum_apply]

/-- Count-independent differentiated dyadic summation. The finite branch
constant depends on the order and primitive channel constants only. The
frequency exponent is exactly `s+1/2`, and the norm is that of the original
`WideInput`, not a sum of its component norms
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_gradedWideBandOperatorSum_rounded_le
    {K L : ℝ} (hK : 1 ≤ K) (hL : 1 ≤ L) (hLK : L ≤ K)
    (T : SliceDerivativeBranch s → (j : Fin (cutoffCount K)) → WideBandL2 n j.val →L[ℂ] E)
    (B : SliceDerivativeBranch s → ℝ) (hB : ∀ b, 0 ≤ B b)
    (hT : ∀ b j, ‖T b j‖ ^ 2 ≤ B b * (2 : ℝ) ^ j.val) :
    ‖gradedWideBandOperatorSum T L‖ ≤
      (2 * (4 : ℝ) ^ s * ∑ b, Real.sqrt (B b)) * K ^ ((s : ℝ) + 1 / 2) := by
  have hK0 : 0 ≤ K := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hb (b : SliceDerivativeBranch s) :
      ‖wideBandOperatorSum (fun j ↦
        (((2 : ℝ) ^ j.val) ^ b.phaseCount * L ^ (s - b.phaseCount)) • T b j)‖ ≤
        (2 * (4 : ℝ) ^ s * Real.sqrt (B b)) * K ^ s * Real.sqrt K := by
    let g : Fin (cutoffCount K) → ℝ := fun j ↦
      ((2 : ℝ) ^ j.val) ^ b.phaseCount * L ^ (s - b.phaseCount)
    have hg (j : Fin (cutoffCount K)) : g j ≤ (4 : ℝ) ^ s * K ^ s := by
      apply phaseAmplitudeGrade_le_ceiling (by positivity) hL0 (by norm_num) hLK
        ((pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt j.isLt)).trans (cutoffCount_ceiling hK))
        b.phaseCount_le
    have hg0 (j : Fin (cutoffCount K)) : 0 ≤ g j := by dsimp [g]; positivity
    have ht (j : Fin (cutoffCount K)) :
        ‖g j • T b j‖ ^ 2 ≤ (((4 : ℝ) ^ s * K ^ s) ^ 2 * B b) * (2 : ℝ) ^ j.val := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hg0 j), mul_pow]
      calc
        g j ^ 2 * ‖T b j‖ ^ 2 ≤ ((4 : ℝ) ^ s * K ^ s) ^ 2 *
            (B b * (2 : ℝ) ^ j.val) :=
          mul_le_mul (pow_le_pow_left₀ (hg0 j) (hg j) 2) (hT b j)
            (sq_nonneg _) (sq_nonneg _)
        _ = _ := by ring
    have hsq := norm_wideBandOperatorSum_rounded_sq_le hK
      (mul_nonneg (sq_nonneg _) (hB b)) (fun j ↦ g j • T b j) ht
    have he : ((2 * (4 : ℝ) ^ s * Real.sqrt (B b)) * K ^ s * Real.sqrt K) ^ 2 =
        (4 * (((4 : ℝ) ^ s * K ^ s) ^ 2 * B b)) * K := by
      simp only [mul_pow, Real.sq_sqrt (hB b), Real.sq_sqrt hK0]
      ring
    have hn : 0 ≤ (2 * (4 : ℝ) ^ s * Real.sqrt (B b)) * K ^ s * Real.sqrt K := by positivity
    change ‖wideBandOperatorSum (fun j ↦ g j • T b j)‖ ≤ _
    nlinarith [norm_nonneg (wideBandOperatorSum (fun j ↦ g j • T b j))]
  calc
    ‖gradedWideBandOperatorSum T L‖ ≤ ∑ b : SliceDerivativeBranch s,
        ‖wideBandOperatorSum (fun j ↦
          (((2 : ℝ) ^ j.val) ^ b.phaseCount * L ^ (s - b.phaseCount)) • T b j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ b : SliceDerivativeBranch s,
        (2 * (4 : ℝ) ^ s * Real.sqrt (B b)) * K ^ s * Real.sqrt K :=
      Finset.sum_le_sum (fun b _ ↦ hb b)
    _ = (2 * (4 : ℝ) ^ s * ∑ b, Real.sqrt (B b)) * K ^ ((s : ℝ) + 1 / 2) := by
      rw [Real.rpow_add (by linarith : 0 < K), Real.rpow_natCast, ← Real.sqrt_eq_rpow]
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      ring

end JanetCartan.RawPrimary.SliceBounds
