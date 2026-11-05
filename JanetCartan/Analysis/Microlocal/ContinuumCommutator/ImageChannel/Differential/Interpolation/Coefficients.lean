module

public import JanetCartan.Analysis.ContDiff.Norm.Composition.FlowForcing.Profiles
public import JanetCartan.Analysis.Fourier.Periodic.Calculus
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Coefficient interpolation from primitive global jets

The image-normal commutator has two varying scalar coefficient factors. For
`app:ch_background:eq:bg-commutator`, each spends only derivatives above the
first-derivative baseline. The proved closed-ball interpolation underlying
`app:lem:elementary-interpolation-jets` gives a common power profile on the
fundamental cell, including both endpoints and zero order.
-/

public noncomputable section

open scoped ContDiff

namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential

private theorem cNorm_le_jet_budget {n m : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    cNorm S m f ≤ (m + 1 : ℝ) * B := by
  simpa using cNorm_le_sum_of_bounds (fun _ _ ↦ hB) (fun j hj x _ ↦ hf j hj x)

/-- Primitive global coefficient jets give the baseline-one power profile
needed by the image term of `app:ch_background:eq:bg-commutator`.
This uses the proved `app:lem:elementary-interpolation-jets` estimate. -/
theorem exists_coefficient_jet_profile (n s : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : Torus n → ℝ, IsSmoothPeriodic a →
      ∀ H : ℝ, 0 ≤ H →
      (∀ j ≤ 1, ∀ x, ‖iteratedFDeriv ℝ j (periodicLift a) x‖ ≤ M) →
      (∀ j ≤ s + 1, ∀ x, ‖iteratedFDeriv ℝ j (periodicLift a) x‖ ≤ H) →
      ∀ p ≤ s + 1, cNorm (fundamentalCell n) p (periodicLift a) ≤
        K * (1 + H) ^ (((p - 1 : ℕ) : ℝ) / s) := by
  by_cases hs : s = 0
  · subst s
    refine ⟨1 + 2 * M, by positivity, ?_⟩
    intro a _ H _ hlow _ p hp
    have hb := cNorm_le_jet_budget (S := fundamentalCell n) hM hlow
    have hm := cNorm_mono_order (f := periodicLift a) (s := fundamentalCell n) hp
    simp only [Nat.cast_zero, div_zero, Real.rpow_zero, mul_one]
    norm_num at hb
    linarith
  obtain ⟨ρ, hρ⟩ := (isCompact_fundamentalCell n).isBounded.subset_closedBall
    (0 : EuclideanSpace ℝ (Fin n))
  let R := max 1 ρ
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hcell : fundamentalCell n ⊆ Metric.closedBall 0 R :=
    hρ.trans (Metric.closedBall_subset_closedBall (le_max_right _ _))
  obtain ⟨K, hK, hprofile⟩ := FlowForcing.exists_uniform_cNorm_baseline_one_profile_closedBall
    (F := ℝ) (0 : EuclideanSpace ℝ (Fin n)) hR
    (show 2 ≤ s + 1 by omega) (show 0 ≤ 2 * M by positivity)
  refine ⟨K * (s + 3) + 2 * M + 1, by positivity, ?_⟩
  intro a ha H hH hlow hhigh p hp
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hlow' : cNorm (Metric.closedBall 0 R) 1 (periodicLift a) ≤ 2 * M := by
    simpa only [Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num] using
      cNorm_le_jet_budget (S := Metric.closedBall 0 R) hM hlow
  have hhigh' : cNorm (Metric.closedBall 0 R) (s + 1) (periodicLift a) ≤
      (s + 2 : ℝ) * H := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using
      cNorm_le_jet_budget (S := Metric.closedBall 0 R) hH hhigh
  by_cases hp0 : p = 0
  · subst p
    simp only [Nat.zero_sub, Nat.cast_zero, zero_div, Real.rpow_zero, mul_one]
    have hb := cNorm_le_jet_budget (S := fundamentalCell n) hM hlow
    have hm := cNorm_mono_order (f := periodicLift a) (s := fundamentalCell n) (Nat.zero_le 1)
    norm_num at hb
    nlinarith [mul_nonneg hK0 (show (0 : ℝ) ≤ s + 3 by positivity)]
  have hp1 : 1 ≤ p := by omega
  have hspos : 0 < (s : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hθ : 0 ≤ ((p - 1 : ℕ) : ℝ) / s := by positivity
  have hθ' : ((p - 1 : ℕ) : ℝ) / s ≤ 1 := by
    apply (div_le_one hspos).mpr
    exact_mod_cast (show p - 1 ≤ s by omega)
  have hi := hprofile (periodicLift a) ha.2 hlow' p hp1 hp
  have he : ((p : ℝ) - 1) / ((s + 1 : ℕ) - 1) = ((p - 1 : ℕ) : ℝ) / s := by
    rw [Nat.cast_sub hp1]
    simp
  rw [he] at hi
  have hbase : 1 + cNorm (Metric.closedBall 0 R) (s + 1) (periodicLift a) ≤
      (s + 3 : ℝ) * (1 + H) := by nlinarith
  have hconstant : (s + 3 : ℝ) ^ (((p - 1 : ℕ) : ℝ) / s) ≤ s + 3 := by
    have hthree : (1 : ℝ) ≤ s + 3 := by
      have := Nat.cast_nonneg (α := ℝ) s
      linarith
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hthree hθ'
  have hpow : (1 + cNorm (Metric.closedBall 0 R) (s + 1) (periodicLift a)) ^
      (((p - 1 : ℕ) : ℝ) / s) ≤
        (s + 3 : ℝ) * (1 + H) ^ (((p - 1 : ℕ) : ℝ) / s) := by
    calc
      _ ≤ ((s + 3 : ℝ) * (1 + H)) ^ (((p - 1 : ℕ) : ℝ) / s) :=
        Real.rpow_le_rpow
          (by linarith [cNorm_nonneg (Metric.closedBall 0 R) (s + 1) (periodicLift a)]) hbase hθ
      _ = (s + 3 : ℝ) ^ (((p - 1 : ℕ) : ℝ) / s) *
          (1 + H) ^ (((p - 1 : ℕ) : ℝ) / s) :=
        Real.mul_rpow (by positivity) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hconstant (by positivity)
  have hm := cNorm_mono_set (r := p) hcell (isCompact_closedBall 0 R)
    (ha.2.of_le (by simp))
  apply (hm.trans hi).trans
  apply (mul_le_mul_of_nonneg_left hpow hK0).trans
  calc
    _ = (K * (s + 3)) * (1 + H) ^ (((p - 1 : ℕ) : ℝ) / s) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end JanetCartan.ContinuumCommutator.ImageChannel.Differential
