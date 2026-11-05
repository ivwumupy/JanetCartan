module
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Frequency
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
/-!
# Finite frequency derivative bounds

The finite divergence in `app:ch_regular_base:eq:actual-pdo-remainder` loses
exactly one frequency derivative at every order. Constants record the dimension
and the fixed `2π` phase normalization.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.Pseudodifferential
variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: contraction of one frequency
derivative costs at most the dimension, uniformly in the derivative order. -/
theorem norm_iteratedFDeriv_frequencyDivergence_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (B : V → V →L[ℝ] F) (n : ℕ)
    (hB : ContDiff ℝ (n + 1) B) (ξ : V) :
    ‖iteratedFDeriv ℝ n (frequencyDivergence b B) ξ‖ ≤
      Fintype.card ι * ‖iteratedFDeriv ℝ (n + 1) B ξ‖ := by
  have hD : ContDiff ℝ n (fderiv ℝ B) := hB.fderiv_right (m := n) (by simp)
  have hj (j : ι) : ContDiff ℝ n (fun ξ ↦ (fderiv ℝ B ξ (b j)) (b j)) :=
    (hD.clm_apply contDiff_const).clm_apply contDiff_const
  unfold frequencyDivergence
  rw [iteratedFDeriv_fun_sum_apply (fun j _ ↦ (hj j).contDiffAt)]
  calc
    _ ≤ ∑ j, ‖iteratedFDeriv ℝ n (fun ξ ↦ (fderiv ℝ B ξ (b j)) (b j)) ξ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : ι, ‖iteratedFDeriv ℝ (n + 1) B ξ‖ := by
      apply Finset.sum_le_sum
      intro j _
      have h₁ := norm_iteratedFDeriv_clm_apply_const
        (c := b j) (x := ξ) (f := fun η ↦ fderiv ℝ B η (b j)) (hD.clm_apply contDiff_const).contDiffAt (le_refl (n : WithTop ℕ∞))
      have h₂ := norm_iteratedFDeriv_clm_apply_const
        (c := b j) (x := ξ) hD.contDiffAt (le_refl (n : WithTop ℕ∞))
      simp only [b.norm_eq_one, one_mul, norm_iteratedFDeriv_fderiv] at h₁ h₂
      exact h₁.trans h₂
    _ = _ := by simp [nsmul_eq_mul]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: finite frequency derivative
bounds including the coefficient for unit-frequency Fourier phases. -/
theorem norm_iteratedFDeriv_normalizedFrequencyDivergence_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (B : V → V →L[ℝ] F) (n : ℕ)
    (hB : ContDiff ℝ (n + 1) B) (ξ : V) :
    ‖iteratedFDeriv ℝ n (normalizedFrequencyDivergence b B) ξ‖ ≤
      ‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι *
        ‖iteratedFDeriv ℝ (n + 1) B ξ‖ := by
  let L : F →L[ℝ] F := (2 * Real.pi * Complex.I)⁻¹ • ContinuousLinearMap.id ℝ F
  have hD : ContDiff ℝ n (frequencyDivergence b B) := by
    apply ContDiff.sum
    intro j _
    exact ((hB.fderiv_right (m := n) (by simp)).clm_apply
      contDiff_const).clm_apply contDiff_const
  change ‖iteratedFDeriv ℝ n (L ∘ frequencyDivergence b B) ξ‖ ≤ _
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ n (frequencyDivergence b B) ξ‖ :=
      L.norm_iteratedFDeriv_comp_left hD.contDiffAt (by rfl)
    _ ≤ ‖(2 * Real.pi * Complex.I)⁻¹‖ *
        (Fintype.card ι * ‖iteratedFDeriv ℝ (n + 1) B ξ‖) := by
      gcongr
      · exact (ContinuousLinearMap.opNorm_smul_le _ _).trans
          (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le)
      · exact norm_iteratedFDeriv_frequencyDivergence_le b B n hB ξ
    _ = _ := by ring
end JanetCartan.Pseudodifferential
