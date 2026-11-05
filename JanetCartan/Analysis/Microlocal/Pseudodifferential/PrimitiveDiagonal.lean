module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.OscillatoryDiagonal

/-!
# Diagonal reduction from finite primitive symbol bounds

For `app:ch_regular_base:eq:actual-pdo-remainder`, the actual unregularized
identity follows from polynomial bounds on finitely many derivatives of the
primitive amplitude. The Taylor coefficient costs one derivative and the full
remainder costs two; both physical positions and the source mask are retained.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.Pseudodifferential
universe u v
variable {V : Type u} {F : Type (max u v)} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the source derivatives of
the Taylor coefficient obey an explicit finite polynomial-growth bound, using
primitive order `n + 1` and retaining every source-mask derivative. -/
theorem norm_iteratedFDeriv_fullTaylorCoefficient_source_le
    (c : V → V → V → F) (β : V → ℝ)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (x y ξ : V) (n m : ℕ) (M K : ℕ → ℝ)
    (hM : ∀ j ≤ n + 1, ∀ z, ‖iteratedFDeriv ℝ j
      (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2) (x, z, ξ)‖ ≤ M j * (1 + ‖ξ‖) ^ m)
    (hK : ∀ j ≤ n, ‖iteratedFDeriv ℝ j β y‖ ≤ K j) :
    ‖iteratedFDeriv ℝ n (fun z ↦ fullTaylorCoefficient c β x z ξ) y‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * K i * M (n - i + 1)) *
        (1 + ‖ξ‖) ^ m := by
  apply (norm_iteratedFDeriv_source_le_joint _ (contDiff_fullTaylorCoefficient_joint c β hc hβ)
    x y ξ n).trans
  have hh := norm_iteratedFDeriv_fullTaylorCoefficient_joint_le c β hc hβ (x, y, ξ) n
    (fun k ↦ M (k + 1) * (1 + ‖ξ‖) ^ m) (fun k hk t _ ↦ ?_)
  · apply hh.trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hMn : 0 ≤ M (n - i + 1) * (1 + ‖ξ‖) ^ m :=
      (norm_nonneg _).trans (hM _ (by omega) y)
    calc
      _ ≤ (n.choose i : ℝ) * K i * (M (n - i + 1) * (1 + ‖ξ‖) ^ m) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hK i hi') (by positivity)) hMn
      _ = _ := by ring
  · change ‖iteratedFDeriv ℝ (k + 1) (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2)
      (x, (1 - t) • x + t • y, ξ)‖ ≤ _
    exact hM _ (by omega) _

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the complete remainder's
source bounds use primitive order `n + 2`, with its normalization and dimension
explicit. These bounds suffice for frequency convergence after source testing. -/
theorem norm_iteratedFDeriv_diagonalRemainderAmplitude_source_le
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β : V → ℝ)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (x y ξ : V) (n m : ℕ) (M K : ℕ → ℝ)
    (hM : ∀ j ≤ n + 2, ∀ z, ‖iteratedFDeriv ℝ j
      (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2) (x, z, ξ)‖ ≤ M j * (1 + ‖ξ‖) ^ m)
    (hK : ∀ j ≤ n + 1, ‖iteratedFDeriv ℝ j β y‖ ≤ K j) :
    ‖iteratedFDeriv ℝ n (fun z ↦ diagonalRemainderAmplitude b c β x z ξ) y‖ ≤
      (‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι *
        ∑ i ∈ Finset.range (n + 2), ((n + 1).choose i : ℝ) * K i * M (n + 1 - i + 1)) *
          (1 + ‖ξ‖) ^ m := by
  apply (norm_iteratedFDeriv_source_le_joint _
    (contDiff_diagonalRemainderAmplitude_joint b c β hc hβ) x y ξ n).trans
  have hh := norm_iteratedFDeriv_diagonalRemainderAmplitude_joint_le b c β hc hβ (x, y, ξ) n
    (fun k ↦ M (k + 1) * (1 + ‖ξ‖) ^ m) (fun k hk t _ ↦ ?_)
  · apply hh.trans
    rw [mul_assoc _ _ ((1 + ‖ξ‖) ^ m), Finset.sum_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ n + 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hMn : 0 ≤ M (n + 1 - i + 1) * (1 + ‖ξ‖) ^ m :=
      (norm_nonneg _).trans (hM _ (by omega) y)
    calc
      _ ≤ ((n + 1).choose i : ℝ) * K i * (M (n + 1 - i + 1) * (1 + ‖ξ‖) ^ m) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hK i hi') (by positivity)) hMn
      _ = _ := by ring
  · change ‖iteratedFDeriv ℝ (k + 1) (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2)
      (x, (1 - t) • x + t • y, ξ)‖ ≤ _
    exact hM _ (by omega) _


omit [FiniteDimensional ℝ V] in
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the diagonal term's source
derivatives fall entirely on the fixed source mask. -/
theorem norm_iteratedFDeriv_diagonalAmplitude_source_le
    (c : V → V → V → F) (β : V → ℝ) (hβ : ContDiff ℝ ∞ β) (x y ξ : V) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z ↦ diagonalAmplitude c β x z ξ) y‖ ≤
      ‖iteratedFDeriv ℝ n β y‖ * ‖c x x ξ‖ := by
  have h := (ContinuousLinearMap.toSpanSingleton ℝ (c x x ξ)).norm_iteratedFDeriv_comp_left
    (x := y) hβ.contDiffAt (n := n) (by simp)
  simpa only [diagonalAmplitude, Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.norm_toSpanSingleton, mul_comm] using h

variable [MeasurableSpace V] [BorelSpace V] [CompleteSpace F]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: exact diagonal reduction
from primitive polynomial symbol bounds, with every convergence premise
discharged. For growth order `m`, source testing uses `m + dim V + 1`
derivatives and the primitive amplitude is used only through `m + dim V + 3`.
The two additional derivatives are the fixed Taylor/remainder shift. -/
theorem fullAmplitudeOperator_eq_diagonal_add_remainder_of_symbolBounds
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β : V → ℝ) (u : V → ℂ) (x : V) (m : ℕ)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (hβs : HasCompactSupport β)
    (hβc : ∀ ξ z, c x z ξ ≠ 0 → β z = 1)
    (hu : ContDiff ℝ (m + Module.finrank ℝ V + 1) u) (huc : HasCompactSupport u)
    (M : ℕ → ℝ) (hM : ∀ j ≤ m + Module.finrank ℝ V + 3, ∀ y ξ,
      ‖iteratedFDeriv ℝ j (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2) (x, y, ξ)‖ ≤
        M j * (1 + ‖ξ‖) ^ m) :
    fullAmplitudeOperator c u x = fullAmplitudeOperator (diagonalAmplitude c β) u x +
      fullAmplitudeOperator (diagonalRemainderAmplitude b c β) u x := by
  classical
  have hbounds (j : ℕ) : ∃ K : ℝ, ∀ y, ‖iteratedFDeriv ℝ j β y‖ ≤ K :=
    (hβs.iteratedFDeriv j).exists_bound_of_continuous (hβ.continuous_iteratedFDeriv (by simp))
  choose K hK using hbounds
  have hd : ContDiff ℝ ∞ (fun p : V × V × V ↦ diagonalAmplitude c β p.1 p.2.1 p.2.2) :=
    (hβ.comp contDiff_snd.fst).smul
      (hc.comp (f := fun p : V × V × V ↦ (p.1, p.1, p.2.2)) (by fun_prop))
  have hr := contDiff_diagonalRemainderAmplitude_joint b c β hc hβ
  have hB := contDiff_fullTaylorCoefficient_joint c β hc hβ
  apply fullAmplitudeOperator_eq_diagonal_add_remainder b c β u x hc hβ hβc hu.continuous huc
  · apply integrable_sourceAmplitudeTransform_of_sourceSymbolBounds c u x m
      (hc.continuous.comp (f := fun p : V × V ↦ (x, p.2, p.1)) (by fun_prop)) hu huc
      (fun ξ ↦ (hc.comp (f := fun y : V ↦ (x, y, ξ)) (by fun_prop)).of_le (by simp)) M
    intro j hj y ξ
    exact (norm_iteratedFDeriv_source_le_joint c hc x y ξ j).trans (hM j (by omega) y ξ)
  · apply integrable_sourceAmplitudeTransform_of_sourceSymbolBounds _ u x m
      (hd.continuous.comp (f := fun p : V × V ↦ (x, p.2, p.1)) (by fun_prop)) hu huc
      (fun ξ ↦ (hd.comp (f := fun y : V ↦ (x, y, ξ)) (by fun_prop)).of_le (by simp))
      (fun j ↦ K j * M 0)
    intro j _ y ξ
    have h0 : ‖c x x ξ‖ ≤ M 0 * (1 + ‖ξ‖) ^ m := by
      simpa only [norm_iteratedFDeriv_zero] using hM 0 (by omega) x ξ
    calc
      _ ≤ ‖iteratedFDeriv ℝ j β y‖ * ‖c x x ξ‖ :=
        norm_iteratedFDeriv_diagonalAmplitude_source_le c β hβ x y ξ j
      _ ≤ K j * (M 0 * (1 + ‖ξ‖) ^ m) :=
        mul_le_mul (hK j y) h0 (norm_nonneg _) ((norm_nonneg _).trans (hK j y))
      _ = _ := by ring
  · apply integrable_sourceAmplitudeTransform_of_sourceSymbolBounds _ u x m
      (hr.continuous.comp (f := fun p : V × V ↦ (x, p.2, p.1)) (by fun_prop)) hu huc
      (fun ξ ↦ (hr.comp (f := fun y : V ↦ (x, y, ξ)) (by fun_prop)).of_le (by simp))
      (fun j ↦ ‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι *
        ∑ i ∈ Finset.range (j + 2), ((j + 1).choose i : ℝ) * K i * M (j + 1 - i + 1))
    intro j hj y ξ
    exact norm_iteratedFDeriv_diagonalRemainderAmplitude_source_le b c β hc hβ x y ξ j m M K
      (fun k hk z ↦ hM k (by omega) z ξ) (fun k _ ↦ hK k y)
  · apply integrable_sourceAmplitudeTransform_of_sourceSymbolBounds _ u x m
      (hB.continuous.comp (f := fun p : V × V ↦ (x, p.2, p.1)) (by fun_prop)) hu huc
      (fun ξ ↦ (hB.comp (f := fun y : V ↦ (x, y, ξ)) (by fun_prop)).of_le (by simp))
      (fun j ↦ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * K i * M (j - i + 1))
    intro j hj y ξ
    exact norm_iteratedFDeriv_fullTaylorCoefficient_source_le c β hc hβ x y ξ j m M K
      (fun k hk z ↦ hM k (by omega) z ξ) (fun k _ ↦ hK k y)

end JanetCartan.Pseudodifferential
