module

public import JanetCartan.Analysis.PhysicalBernstein
public import JanetCartan.Iteration.RevisedGlobal.History
public import JanetCartan.Iteration.RevisedConvergence.Rates

/-!
# Physical Bernstein budgets on an actual finite prefix

`main:eq:history-bernstein` and `main:eq:final-Cr` for the real global fields of
`RevisedGlobal.IsAdmissibleHistory`. The input is exact radian Fourier support
and the absorbed physical L² bound. The derivative bounds are proved, not part
of the history predicate. Constants are fixed before the initial scale, the
order labels, and the increments.
-/

@[expose] public noncomputable section

namespace JanetCartan.PhysicalHistory

open PhysicalBernstein RevisedConvergence

/-- The fixed `C_r` in the physical seminorm form of `main:eq:history-bernstein`.
The sum accounts for the project's sum-of-suprema `cNorm` convention. -/
def seminormConstant (n r : ℕ) (B : ℝ) : ℝ :=
  ∑ d ∈ Finset.range (r + 1), bernsteinConstant n d * B ^ ((d : ℝ) + (n : ℝ) / 2)

/-- The coefficient of the positive scale power in `main:eq:history-bernstein`
is nonnegative at the fixed band constant. -/
theorem seminormConstant_nonneg (n r : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ seminormConstant n r B :=
  Finset.sum_nonneg (fun d _ ↦ mul_nonneg (bernsteinConstant_pos n d).le (Real.rpow_nonneg hB _))

/-- `main:eq:final-Cr` on the same field at an arbitrary earlier index of a
finite admissible history. The estimate holds on *any* physical subset, in
particular on the whole space. No stage-dependent Bernstein constant occurs. -/
theorem cNorm_prefix_increment_le {n N j kMin : ℕ} {B R₀ : ℝ}
    {u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)} {ell : Fin j → ℕ}
    (hu : RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell) (hB : 1 ≤ B) (hR₀ : 1 ≤ R₀)
    (K : Set (Euclidean n)) (r : ℕ) (i : Fin j) :
    cNorm K r (u i) ≤ seminormConstant n r B * iterationScale R₀ growthExponent i.val ^
      (-(ell i : ℝ) + derivativeLoss n r) := by
  let R := iterationScale R₀ growthExponent i.val
  let D (d : ℕ) := bernsteinConstant n d * B ^ ((d : ℝ) + (n : ℝ) / 2)
  have hBpos := zero_lt_one.trans_le hB
  have hRone : 1 ≤ R := one_le_scale hR₀ i.val
  have hRpos := zero_lt_one.trans_le hRone
  have hΛ : 0 < B * R ^ bandExponent := mul_pos hBpos (Real.rpow_pos_of_pos hRpos _)
  have hD (d : ℕ) : 0 ≤ D d :=
    mul_nonneg (bernsteinConstant_pos n d).le (Real.rpow_nonneg hBpos.le _)
  calc
    _ ≤ ∑ d ∈ Finset.range (r + 1), D d * R ^ (-(ell i : ℝ) + derivativeLoss n r) := by
      apply cNorm_le_sum_of_bounds (fun d _ ↦ mul_nonneg (hD d) (Real.rpow_nonneg hRpos.le _))
      intro d hd x _
      have hder := derivative_bound_of_physical_bounds hRpos hBpos.le (bernsteinConstant_pos n d).le
        (norm_iteratedFDeriv_le (u i) hΛ (hu i).2.1 d x) (hu i).2.2
      apply hder.trans
      apply mul_le_mul_of_nonneg_left _ (hD d)
      apply Real.rpow_le_rpow_of_exponent_le hRone
      apply add_le_add_right
      unfold derivativeLoss
      apply add_le_add_right
      exact mul_le_mul_of_nonneg_left (add_le_add_left (Nat.cast_le.mpr hd) _)
        (by norm_num [bandExponent])
    _ = _ := (Finset.sum_mul ..).symm

end JanetCartan.PhysicalHistory
