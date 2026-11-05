module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.SupportedBudgets

/-!
# Physical restriction of retained background jets

The physical restriction in `app:ch_waves:eq:background-quadrature-rough`
freezes the inverse frequency and the original carrier covector. It is an
affine contraction, so the joint jet reserve gives the physical bound with
no derivative loss. The actual producer is
`exists_retained_supportedBackground_budgets`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.Sampling.RetainedBackground
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets

variable {X Z V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Restricting a joint background jet to its physical variable costs no
norm factor (`app:ch_waves:eq:background-quadrature-rough`). -/
theorem norm_iteratedFDeriv_physicalSlice_le
    {H : ℝ × (X × Z) → V} (hH : ContDiff ℝ ∞ H)
    (τ : ℝ) (z : Z) (x : X) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ H (τ, (y, z))) x‖ ≤
      ‖iteratedFDeriv ℝ j H (τ, (x, z))‖ := by
  let A : X →L[ℝ] ℝ × (X × Z) :=
    (ContinuousLinearMap.inr ℝ ℝ (X × Z)).comp (ContinuousLinearMap.inl ℝ X Z)
  have hA : ‖A‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (ContinuousLinearMap.norm_inr_le_one ..)
        (ContinuousLinearMap.norm_inl_le_one ..) (norm_nonneg _) zero_le_one).trans_eq
          (one_mul 1))
  have hh := norm_iteratedFDeriv_preAffine_le A (τ, (0, z)) isOpen_univ
    hH.contDiffOn (x := x) (mem_univ _) j
  have hh' : ‖iteratedFDeriv ℝ j (fun y ↦ H (τ, (y, z))) x‖ ≤
      ‖iteratedFDeriv ℝ j H (τ, (x, z))‖ * ‖A‖ ^ j := by
    simpa [A] using hh
  exact hh'.trans
    (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg A) hA))

/-- The physical `C^r` bound follows from the retained joint profile. Its
constant is the fixed finite sum of jet constants, before `L`, the frequency
and the carrier (`app:ch_waves:eq:background-quadrature-rough`). -/
theorem cNorm_physicalSlice_le
    {H : ℝ × (X × Z) → V} (hH : ContDiff ℝ ∞ H)
    {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) {L : ℝ} (hL : 1 ≤ L)
    {rpar : ℕ}
    (hj : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w, ∀ j,
      ‖iteratedFDeriv ℝ j H (τ, w)‖ ≤ A j * L ^ (j - rpar))
    {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (z : Z) (K : Set X) (r : ℕ) :
    cNorm K r (fun x ↦ H (τ, (x, z))) ≤
      (∑ j ∈ Finset.range (r + 1), A j) * L ^ r := by
  rw [Finset.sum_mul]
  apply cNorm_le_sum_of_bounds (fun j _ ↦ mul_nonneg (hA j)
    (pow_nonneg (zero_le_one.trans hL) _))
  intro j hjr x _
  exact ((norm_iteratedFDeriv_physicalSlice_le hH τ z x j).trans
    (hj τ hτ (x, z) j)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL
        ((Nat.sub_le j rpar).trans hjr)) (hA j))

end JanetCartan.Sampling.RetainedBackground
