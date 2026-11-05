module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Cutoffs

/-!
# Derivative profiles of the fixed physical cutoffs

The constants below are chosen from `frequencyBump` alone. These are the
cutoff-jet inputs to the comparable and noncomparable pair estimates in
`app:ch_regular:eq:chain-tail`; they do not depend on shell indices or accuracy.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.FiniteChain.Graph.PhysicalShells
variable {n : ℕ}

/-- A derivative bound obtained from the actual fixed bump, for
`app:ch_regular:eq:chain-tail`. -/
def frequencyBumpDerivativeBound (n m : ℕ) : ℝ :=
  ((frequencyBump n).hasCompactSupport.exists_bound_iteratedFDeriv
    (frequencyBump n).contDiff m).choose

/-- Positivity of the fixed bump profile (`app:ch_regular:eq:chain-tail`). -/
theorem frequencyBumpDerivativeBound_nonneg (n m : ℕ) :
    0 ≤ frequencyBumpDerivativeBound n m :=
  ((frequencyBump n).hasCompactSupport.exists_bound_iteratedFDeriv
    (frequencyBump n).contDiff m).choose_spec.1

/-- The chosen constants bound all actual derivatives through the given order
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_frequencyBump_le (m i : ℕ) (hi : i ≤ m) (ξ : Euclidean n) :
    ‖iteratedFDeriv ℝ i (frequencyBump n) ξ‖ ≤ frequencyBumpDerivativeBound n m :=
  ((frequencyBump n).hasCompactSupport.exists_bound_iteratedFDeriv
    (frequencyBump n).contDiff m).choose_spec.2 i hi ξ

/-- Expanding cutoff derivatives decay at their physical radius
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_expandingCutoff_le (j m : ℕ) (ξ : Euclidean n) :
    ‖iteratedFDeriv ℝ m (expandingCutoff j) ξ‖ ≤
      (((2 : ℝ) ^ j)⁻¹) ^ m * frequencyBumpDerivativeBound n m := by
  change ‖iteratedFDeriv ℝ m (fun ξ : Euclidean n =>
    frequencyBump n (((2 : ℝ) ^ j)⁻¹ • ξ)) ξ‖ ≤ _
  rw [iteratedFDeriv_comp_const_smul _ (frequencyBump n).contDiff,
    norm_smul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_frequencyBump_le m m le_rfl _)
    (by positivity)

/-- Contracting cutoff derivatives have the reciprocal physical scale
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_contractingCutoff_le (j m : ℕ) (ξ : Euclidean n) :
    ‖iteratedFDeriv ℝ m (contractingCutoff j) ξ‖ ≤
      ((2 : ℝ) ^ j) ^ m * frequencyBumpDerivativeBound n m := by
  change ‖iteratedFDeriv ℝ m (fun ξ : Euclidean n =>
    frequencyBump n ((2 : ℝ) ^ j • ξ)) ξ‖ ≤ _
  rw [iteratedFDeriv_comp_const_smul _ (frequencyBump n).contDiff,
    norm_smul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_frequencyBump_le m m le_rfl _)
    (by positivity)

/-- The high annulus derivative profile, uniformly in its shell index
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_highGraphCutoff_le (j m : ℕ) (ξ : Euclidean n) :
    ‖iteratedFDeriv ℝ m (highGraphCutoff j) ξ‖ ≤
      2 * frequencyBumpDerivativeBound n m * (((2 : ℝ) ^ j)⁻¹) ^ m := by
  change ‖iteratedFDeriv ℝ m (expandingCutoff (j + 1) - expandingCutoff j) ξ‖ ≤ _
  rw [iteratedFDeriv_sub_apply
    ((contDiff_expandingCutoff (j + 1)).contDiffAt.of_le (by simp))
    ((contDiff_expandingCutoff j).contDiffAt.of_le (by simp))]
  apply (norm_sub_le _ _).trans
  have hi : ((2 : ℝ) ^ (j + 1))⁻¹ ≤ ((2 : ℝ) ^ j)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  have hp := pow_le_pow_left₀ (by positivity) hi m
  have hb := frequencyBumpDerivativeBound_nonneg n m
  have h₁ := (norm_iteratedFDeriv_expandingCutoff_le (j + 1) m ξ).trans
    (mul_le_mul_of_nonneg_right hp hb)
  have h₂ := norm_iteratedFDeriv_expandingCutoff_le j m ξ
  nlinarith

/-- The low annulus derivative profile includes its shrinking radius; no
uniform-in-radius bound is assumed (`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_lowGraphCutoff_le (j m : ℕ) (ξ : Euclidean n) :
    ‖iteratedFDeriv ℝ m (lowGraphCutoff j) ξ‖ ≤
      (1 + (2 : ℝ) ^ m) * frequencyBumpDerivativeBound n m * ((2 : ℝ) ^ j) ^ m := by
  change ‖iteratedFDeriv ℝ m (contractingCutoff j - contractingCutoff (j + 1)) ξ‖ ≤ _
  rw [iteratedFDeriv_sub_apply
    ((contDiff_contractingCutoff j).contDiffAt.of_le (by simp))
    ((contDiff_contractingCutoff (j + 1)).contDiffAt.of_le (by simp))]
  apply (norm_sub_le _ _).trans
  have h := add_le_add (norm_iteratedFDeriv_contractingCutoff_le j m ξ)
    (norm_iteratedFDeriv_contractingCutoff_le (j + 1) m ξ)
  convert h using 1
  simp only [pow_succ, mul_pow]
  ring

/-- A single profile for all independent output indices, including index zero
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_outputCutoff_le (k m : ℕ) (ξ : Euclidean n) :
    ‖iteratedFDeriv ℝ m (outputCutoff k) ξ‖ ≤
      2 * frequencyBumpDerivativeBound n m * (((2 : ℝ) ^ (k - 1))⁻¹) ^ m := by
  cases k with
  | zero =>
    have h := norm_iteratedFDeriv_expandingCutoff_le 0 m ξ
    simp only [pow_zero, inv_one, one_pow, one_mul] at h
    simpa only [outputCutoff, Nat.zero_sub, pow_zero, inv_one, one_pow, mul_one] using
      h.trans (by linarith [frequencyBumpDerivativeBound_nonneg n m])
  | succ k => simpa only [Nat.add_sub_cancel, outputCutoff] using
      norm_iteratedFDeriv_highGraphCutoff_le k m ξ

/-- The normalized high graph cutoff has precisely the rescaled derivative
profile used by the comparable-pair estimate in `app:ch_regular:eq:chain-tail`. -/
theorem norm_iteratedFDeriv_rescaled_highGraphCutoff_le (j m : ℕ) (ρ : ℝ) (ξ : Euclidean n) :
    ‖iteratedFDeriv ℝ m (fun η => highGraphCutoff j (ρ • η)) ξ‖ ≤
      |ρ| ^ m * (2 * frequencyBumpDerivativeBound n m * (((2 : ℝ) ^ j)⁻¹) ^ m) := by
  rw [iteratedFDeriv_comp_const_smul ρ ((contDiff_highGraphCutoff j).of_le (by simp)),
    norm_smul, norm_pow, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_highGraphCutoff_le j m _) (by positivity)

/-- The normalized low graph cutoff retains its reciprocal shrinking scale;
no accuracy-dependent smoothing is introduced (`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_rescaled_lowGraphCutoff_le (j m : ℕ) (ρ : ℝ) (ξ : Euclidean n) :
    ‖iteratedFDeriv ℝ m (fun η => lowGraphCutoff j (ρ • η)) ξ‖ ≤
      |ρ| ^ m * ((1 + (2 : ℝ) ^ m) * frequencyBumpDerivativeBound n m * ((2 : ℝ) ^ j) ^ m) := by
  rw [iteratedFDeriv_comp_const_smul ρ ((contDiff_lowGraphCutoff j).of_le (by simp)),
    norm_smul, norm_pow, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_lowGraphCutoff_le j m _) (by positivity)

/-- The independently normalized output profile includes the bounded-frequency
ball and is uniform in both shell indices (`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_rescaled_outputCutoff_le (k m : ℕ) (ρ : ℝ) (ξ : Euclidean n) :
    ‖iteratedFDeriv ℝ m (fun η => outputCutoff k (ρ • η)) ξ‖ ≤
      |ρ| ^ m * (2 * frequencyBumpDerivativeBound n m * (((2 : ℝ) ^ (k - 1))⁻¹) ^ m) := by
  rw [iteratedFDeriv_comp_const_smul ρ ((contDiff_outputCutoff k).of_le (by simp)),
    norm_smul, norm_pow, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_outputCutoff_le k m _) (by positivity)

end JanetCartan.FiniteChain.Graph.PhysicalShells
