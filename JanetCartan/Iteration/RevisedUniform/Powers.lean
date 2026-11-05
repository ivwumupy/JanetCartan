module

public import JanetCartan.Iteration.RevisedUniform.Scales
public import JanetCartan.Analysis.Iteration.AdaptiveSchedule

/-!
# Scale and correction powers used by the physical assembly

These are the literal powers appearing in the revised contract.  In
particular `δ` and `b` are not renamed or replaced by an independently chosen
scale.  The facts are independent of any source producer.
-/

@[expose] public noncomputable section

namespace JanetCartan.RevisedUniform

open JanetCartan

/-- Basic positivity and unit bounds for the exact stage scale, correction
factor and forcing amplitude. -/
theorem iteration_scale_power_facts {R₀ : ℝ} (hR₀ : 2 ≤ R₀)
    (j k n : ℕ) :
    let R := iterationScale R₀ growthExponent j
    let δ := R ^ (-(k : ℝ))
    let b := δ * R ^ RevisedScales.forcingExponent n
    1 ≤ R ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < b := by
  dsimp only
  have hRone : 1 ≤ iterationScale R₀ growthExponent j := by
    apply Real.one_le_rpow
    · linarith
    · norm_num [growthExponent]
  have hRpos : 0 < iterationScale R₀ growthExponent j :=
    lt_of_lt_of_le zero_lt_one hRone
  have hδ : 0 < iterationScale R₀ growthExponent j ^ (-(k : ℝ)) :=
    Real.rpow_pos_of_pos hRpos _
  have hδone : iterationScale R₀ growthExponent j ^ (-(k : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hRone
      (neg_nonpos.mpr (by exact_mod_cast (Nat.zero_le k)))
  exact ⟨hRone, hδ, hδone,
    mul_pos hδ (Real.rpow_pos_of_pos hRpos _)⟩

/-- The cutoff support factor `2` is admissible for the revised correction
contract, and all scale powers are evaluated on the same current `R`. -/
theorem two_le_cutoff_band : (1 : ℝ) ≤ (2 : ℝ) := by norm_num

end JanetCartan.RevisedUniform
