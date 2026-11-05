module

public import JanetCartan.Analysis.ContDiff.Norm.Interpolation
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Analysis.ContDiff.Norm.JointBudget.Algebra

/-!
# Interpolation at the adjoint endpoint reserves

The graph uses baseline `2(n+1)+1`; the derivative-trade fields use `2(n+1)`.
This leaf supplies their actual closed-ball interpolation, including `s = 0`,
for `app:ch_background:prop:bg-adjoint`. Its low and high bounds are instantiated
by the fixed-cutoff and rational first-jet constructions in this directory.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Closed-ball interpolation with the exact natural truncated excess and
denominator `max s 1`. The constant precedes the function and the one high
budget. Consumer: the affine graph and rational field profiles of
`app:ch_background:prop:bg-adjoint`. -/
theorem exists_closedBall_reserve_profile
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) (b s : ℕ) (M A : ℝ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (f : E → F), ContDiff ℝ ∞ f →
        cNorm (closedBall x ρ) b f ≤ M →
        ∀ H : ℝ, 1 ≤ H → cNorm (closedBall x ρ) (b+s) f ≤ A * H →
        ∀ i ≤ b+s, ∀ p ∈ closedBall x ρ,
          ‖iteratedFDeriv ℝ i f p‖ ≤ C i * H ^ (((i-b : ℕ) : ℝ) / (max s 1 : ℕ)) := by
  have hconstants (i : ℕ) : ∃ K ≥ (1 : ℝ), ∀ f : E → F, ContDiff ℝ ∞ f →
      b < i → i < b+s → cNorm (closedBall x ρ) i f ≤
        K * cNorm (closedBall x ρ) b f ^ (1 - ((i-b : ℕ) : ℝ) / s) *
          cNorm (closedBall x ρ) (b+s) f ^ (((i-b : ℕ) : ℝ) / s) := by
    by_cases hi : b < i ∧ i < b+s
    · obtain ⟨K, hK, hk⟩ := cNorm_le_interpolation_closedBall (F := F) x hρ hi.1 hi.2
      refine ⟨max K 1, le_max_right _ _, fun f hf _ _ ↦ ?_⟩
      have he₁ : ((i-b : ℕ) : ℝ) = (i : ℝ) - b := Nat.cast_sub hi.1.le
      have he₂ : ((b+s : ℕ) : ℝ) - b = s := by push_cast; ring
      have hh := hk f hf
      rw [← he₁, he₂] at hh
      apply hh.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left K 1)
          (Real.rpow_nonneg (cNorm_nonneg ..) _))
        (Real.rpow_nonneg (cNorm_nonneg ..) _)
    · exact ⟨1, le_rfl, fun _ _ h₁ h₂ ↦ (hi ⟨h₁, h₂⟩).elim⟩
  choose K hK hk using hconstants
  let B := max M 1
  let D := max A 1
  have hB : 1 ≤ B := le_max_right _ _
  have hD : 1 ≤ D := le_max_right _ _
  refine ⟨fun i ↦ K i * B * D, fun i ↦ mul_nonneg (mul_nonneg (zero_le_one.trans (hK i)) (zero_le_one.trans hB)) (zero_le_one.trans hD), ?_⟩
  intro f hf hlow H hH hhigh i hi p hp
  have hDH : 1 ≤ D * H := by nlinarith
  have hhigh' : cNorm (closedBall x ρ) (b+s) f ≤ D * H :=
    hhigh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans hH))
  have hh := JointBudget.interpolation_le_scaled_rpow
    (fun j ↦ cNorm (closedBall x ρ) j f) b s i B (K i) (D*H)
    (fun _ ↦ cNorm_nonneg ..) (fun _ _ h ↦ cNorm_mono_order h) hB (hK i) hDH
    (hlow.trans (le_max_left _ _)) hhigh' hi (hk i f hf)
  have ht1 : ((i-b : ℕ) : ℝ) / s ≤ 1 := by
    by_cases hs : s = 0
    · simp [hs]
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hs : (0 : ℝ) < s)).2
      exact_mod_cast (show i-b ≤ s by omega)
  have ht : ((i-b : ℕ) : ℝ) / s = ((i-b : ℕ) : ℝ) / (max s 1 : ℕ) := by
    by_cases hs : s = 0
    · have hib : i ≤ b := by omega
      simp [hs, Nat.sub_eq_zero_of_le hib]
    · rw [max_eq_left (by omega : 1 ≤ s)]
  have hpow : (D*H) ^ (((i-b : ℕ) : ℝ) / s) ≤
      D * H ^ (((i-b : ℕ) : ℝ) / s) := by
    rw [Real.mul_rpow (zero_le_one.trans hD) (zero_le_one.trans hH)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hD ht1)
      (Real.rpow_nonneg (zero_le_one.trans hH) _)
  have hjet := norm_iteratedFDeriv_le_cNorm (isCompact_closedBall x ρ)
    (hf.of_le (by simp : (i : ℕ∞ω) ≤ ∞)) hp (le_refl i)
  apply (hjet.trans hh).trans
  simpa only [ht, mul_assoc] using mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (zero_le_one.trans (hK i)) (zero_le_one.trans hB))

end JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
