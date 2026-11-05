module

public import JanetCartan.Iteration.PhysicalNormalInverse.ContinuityTransfer

/-!
# A fixed-source tolerance for the actual inverse perturbation identity

Normal comparison also bounds the size of the moving row adjoint. Consequently
the required three tolerances can be chosen from the *fixed* inverse gap and
reference row and datum before the physical history. No norm closeness of the
moving raw row is assumed. Consumer: `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace JanetCartan.PhysicalInverseContinuity
open ContinuumRow CoerciveInverse PhysicalNormalInverse.ContinuityTransfer

/-- The moving row has a uniform norm bound from its normal alone. No estimate
for the *difference* of uncut row operators is implicit in this conclusion. -/
theorem adjoint_norm_le_of_normal_sub_le_one {n : ℕ} {ι : Type*} [Fintype ι]
    (A A₀ : AugmentedInput n ι →L[ℝ] OutputL2 n)
    (h : ‖normalOperator A - normalOperator A₀‖ ≤ 1) :
    ‖A.adjoint‖ ≤ 2 + ‖normalOperator A₀‖ := by
  have hsq : ‖A.adjoint‖ ^ 2 = ‖normalOperator A‖ := by
    simpa only [sq, normalOperator, ContinuousLinearMap.adjoint_adjoint] using
      (ContinuousLinearMap.norm_adjoint_comp_self A.adjoint).symm
  have ht := norm_add_le (normalOperator A - normalOperator A₀) (normalOperator A₀)
  rw [sub_add_cancel] at ht
  nlinarith [norm_nonneg (normalOperator A₀), sq_nonneg (‖A.adjoint‖ - 1)]

/-- One positive tolerance chosen before the current row controls the literal
unconditional raw right inverse on the measured datum. Only the normal,
residual and strong fixed-vector adjoint errors occur. The fixed normal gap
is the original current coercivity lower bound, not an accuracy-dependent
weakened comparison gap. -/
theorem exists_raw_L2_perturbation_tolerance {n : ℕ} {ι : Type*} [Fintype ι]
    (A₀ : AugmentedInput n ι →L[ℝ] OutputL2 n) (e₀ : OutputL2 n)
    {γ γ₀ : ℝ} (hγ : 0 < γ) (hγ₀ : 0 < γ₀)
    (hgap₀ : ∀ w, γ₀ * ‖w‖ ^ 2 ≤ ‖A₀.adjoint w‖ ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ (A : AugmentedInput n ι →L[ℝ] OutputL2 n) (e : OutputL2 n),
      (∀ w, γ * ‖w‖ ^ 2 ≤ ‖A.adjoint w‖ ^ 2) → ‖e - e₀‖ ≤ η →
      ‖normalOperator A - normalOperator A₀‖ ≤ η →
      ‖(A.adjoint - A₀.adjoint) ((normalOperator A₀).inverse e₀)‖ ≤ η →
      ‖rightInverse A e - rightInverse A₀ e₀‖ ≤ ε := by
  let w := (normalOperator A₀).inverse e₀
  let B := 2 + ‖normalOperator A₀‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let D := 1 + B * (γ⁻¹ * (1 + ‖w‖))
  have hD : 0 < D := by dsimp [D]; positivity
  let η := min 1 (ε / D)
  have hη : 0 < η := lt_min zero_lt_one (div_pos hε hD)
  have hηD : η * D ≤ ε := (le_div_iff₀ hD).mp (min_le_right _ _)
  refine ⟨η, hη, ?_⟩
  intro A e hgap he hn ha
  have hA := adjoint_norm_le_of_normal_sub_le_one A A₀ (hn.trans (min_le_left _ _))
  have h := raw_rightInverse_sub_le A A₀ hγ hγ₀ hgap hgap₀ e e₀
  calc
    _ ≤ _ := h
    _ ≤ B * (γ⁻¹ * (η + η * ‖w‖)) + η := add_le_add (mul_le_mul hA
      (mul_le_mul_of_nonneg_left (add_le_add he (mul_le_mul_of_nonneg_right hn (norm_nonneg _)))
        (inv_nonneg.mpr hγ.le)) (by positivity) hB) ha
    _ = η * D := by dsimp only [D]; ring
    _ ≤ ε := hηD

end JanetCartan.PhysicalInverseContinuity
