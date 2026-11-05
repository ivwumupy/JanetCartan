module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Unit
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# All-order bounds for the actual inward smoother

This proves the `C^r` derivative profile in
`app:ch_regular_base:eq:ball-extension-sobolev` directly from the original
closed-ball `C^0` norm. The fixed kernel derivative integrals, finite binomial
coefficients, and checked thin-cutoff profile are the actual producers of
every constant. No positive input derivative is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Metric
open scoped ContDiff

namespace JanetCartan.BallSmoothing

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem norm_regularizedCombination_jet_le {R : ℝ} (hR : 1 ≤ R)
    (m : ℕ) {f : E → F} (hf : ContinuousOn f (closedBall (0 : E) 1))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ closedBall (0 : E) 1, ‖f x‖ ≤ M)
    (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ r (fun z ↦ ∑ j ∈ Finset.Icc 1 m,
      coefficient m j • regularizedAverage (kernel n) R j f z) x‖ ≤
      ((∑ j ∈ Finset.Icc 1 m, |coefficient m j|) *
        ∫ y, ‖iteratedFDeriv ℝ r (kernel n) y‖) * R ^ r * M := by
  have hreg j (hj : j ∈ Finset.Icc 1 m) :
      ContDiff ℝ ∞ (regularizedAverage (kernel n) R j f) :=
    contDiff_regularizedAverage (ne_of_gt (zero_lt_one.trans_le hR))
      (by have := (Finset.mem_Icc.mp hj).1; omega)
      hasCompactSupport_kernel contDiff_kernel hf
  rw [iteratedFDeriv_fun_sum_apply
    (fun j hj ↦ ((hreg j hj).const_smul _).contDiffAt.of_le (by simp))]
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 m, ‖iteratedFDeriv ℝ r
        (fun z ↦ coefficient m j • regularizedAverage (kernel n) R j f z) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 m, |coefficient m j| *
        ((∫ y, ‖iteratedFDeriv ℝ r (kernel n) y‖) * R ^ r * M) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [iteratedFDeriv_const_smul_apply' ((hreg j hj).contDiffAt.of_le (by simp)),
        norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_regularizedAverage_le hR (Finset.mem_Icc.mp hj).1
          hasCompactSupport_kernel contDiff_kernel hf hM hbound r x) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Choose all derivative constants before the varying scale and input for
the actual unit-ball smoother. The output uses the same fixed real kernel,
finite binomial coefficients, and thin cutoff as the approximation theorem
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem exists_unitSmoothing_jet_bounds (n : ℕ) (m : ℕ) (hm : 1 ≤ m) :
    ∃ B : ℕ → ℝ, (∀ r, 0 ≤ B r) ∧
      ∀ R : ℝ, (2 : ℝ) * m ≤ R → ∀ f : EuclideanSpace ℝ (Fin n) → F,
        ContinuousOn f (closedBall 0 1) → ∀ r x,
          ‖iteratedFDeriv ℝ r (unitSmoothing R m f) x‖ ≤
            B r * R ^ r * cNorm (closedBall 0 1) 0 f := by
  obtain ⟨C, hC, hcut, _⟩ := exists_unitCutoff_global_bounds n
  let D (r : ℕ) := (∑ j ∈ Finset.Icc 1 m, |coefficient m j|) *
    ∫ y : EuclideanSpace ℝ (Fin n), ‖iteratedFDeriv ℝ r (kernel n) y‖
  have hD r : 0 ≤ D r := mul_nonneg
    (Finset.sum_nonneg fun j _ ↦ abs_nonneg _) (integral_nonneg fun y ↦ norm_nonneg _)
  let B (r : ℕ) := ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * C j * D (r - j)
  have hB r : 0 ≤ B r := Finset.sum_nonneg fun j _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC j)) (hD _)
  refine ⟨B, hB, ?_⟩
  intro R hR f hf r x
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  let M := cNorm (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) 0 f
  have hM : 0 ≤ M := cNorm_nonneg _ _ _
  have hbound y (hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) : ‖f y‖ ≤ M := by
    dsimp only [M]
    rw [cNorm_order_zero]
    exact le_csSup ((isCompact_closedBall _ _).bddAbove_image hf.norm)
      (mem_image_of_mem _ hy)
  let g : EuclideanSpace ℝ (Fin n) → F := fun z ↦ ∑ j ∈ Finset.Icc 1 m,
    coefficient m j • regularizedAverage (kernel n) R j f z
  have hg : ContDiff ℝ ∞ g := by
    apply ContDiff.sum
    intro j hj
    exact (contDiff_regularizedAverage (ne_of_gt (zero_lt_one.trans_le hR1))
      (by have := (Finset.mem_Icc.mp hj).1; omega)
      hasCompactSupport_kernel contDiff_kernel hf).const_smul _
  have hgj j : ‖iteratedFDeriv ℝ j g x‖ ≤ D j * R ^ j * M :=
    norm_regularizedCombination_jet_le hR1 m hf hM hbound j x
  rw [unitSmoothing_eq_regularized hm hR f]
  apply (norm_iteratedFDeriv_smul_le (unitCutoff_contDiff n R) hg x (by simp)).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (r + 1),
        ((r.choose j : ℝ) * C j * D (r - j)) * R ^ r * M := by
      apply Finset.sum_le_sum
      intro j hj
      have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      calc
        _ ≤ (r.choose j : ℝ) * (C j * R ^ j) * (D (r - j) * R ^ (r - j) * M) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hcut R hR1 j x) (Nat.cast_nonneg _))
            (hgj (r - j)) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC j) (pow_nonneg hR0 _)))
        _ = _ := by
          rw [show R ^ r = R ^ j * R ^ (r - j) by rw [← pow_add, Nat.add_sub_of_le hjr]]
          ring
    _ = B r * R ^ r * M := by simp only [B, Finset.sum_mul]

end JanetCartan.BallSmoothing
