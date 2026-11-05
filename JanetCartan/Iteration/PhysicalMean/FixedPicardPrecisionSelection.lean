module

public import JanetCartan.Iteration.PhysicalMean.SourcePrecision

/-!
# Static choices for the fixed-source finite Picard run

This numerical deduction is the final threshold join of
`app:ch_mean_pairs:prop:mean-iteration`. The FINITE step count and proof-tail
order are chosen before the coefficient profiles. K remains R^fineExponent
for the entire run. Only the real source envelope R^(-separationExponent)
appears; no product bound involving the coefficient scale is used.

The original-data producer obligations are88's low/high linear bounds,
89's low quadratic bound,102's high quadratic profile, and99's forcing
profile with101's pre-source choice pOrder=1. No successful source is assumed.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalMean
open CurrentMean

/-- The actual history's coefficient scale and source envelope satisfy the
numeric hypotheses of the finite profile induction. -/
theorem fixedPicard_history_scale_facts {R₀ : ℝ} (hR₀ : 2 ≤ R₀) (j : ℕ) :
    let R := historyScale R₀ growthExponent j
    let T := currentCoefficientScale R₀ j
    1 ≤ R ∧ 1 ≤ T ∧ T ≤ R ∧ 0 ≤ R ^ (-separationExponent) ∧
      R ^ (-separationExponent) ≤ 1 ∧ 0 < R ^ fineExponent := by
  intro R T
  have hbase : 1 ≤ R₀ := (by norm_num : (1 : ℝ) ≤ 2).trans hR₀
  have hR : 1 ≤ R := hbase.trans (le_historyScale hbase j)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  refine ⟨hR, one_le_currentCoefficientScale hbase j, ?_,
    Real.rpow_nonneg hRp.le _, ?_, Real.rpow_pos_of_pos hRp _⟩
  · change R ^ coefficientExponent ≤ R
    calc
      _ ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR (by norm_num [coefficientExponent])
      _ = R := Real.rpow_one R
  · exact Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num [separationExponent])

/-- Select the finite Picard index and proof-only tail order first. Every
subsequent profile constant and low-defect coefficient is absorbed by one
static threshold. The conclusion is numerical, not a source estimate. -/
theorem exists_fixedPicard_profile_threshold (n : ℕ) (accuracy : ℝ) :
    ∃ N q : ℕ,
      2 * accuracy < ((1 + samplingSlack - fineExponent) / 4) * N ∧
      2 * accuracy < (q : ℝ) * (fineExponent - 1) ∧
      ∀ (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ),
        (∀ s, 0 ≤ Cg s) → (∀ s, 0 ≤ CE s) →
        (∀ A : ℕ → ℝ, (∀ s, 0 ≤ A s) → ∀ s, 0 ≤ CQ A s) →
      ∀ (b c₀ Ca ρ : ℝ), 0 ≤ b → ((1 + samplingSlack - fineExponent) / 4) < ρ →
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R : ℝ, S ≤ R →
        let D := fun s ↦ ∑ k ∈ Finset.range (N+1), sourceIterateProfile Cg CE CQ k s
        Ca * R ^ (-ρ) + 2*c₀*D (n/2+2)*R ^ (-separationExponent) ≤
          R ^ (-((1 + samplingSlack - fineExponent) / 4)) ∧
        (2 * fourierInterpolationConstant n 1 (n/2+2) *
          finiteSourceResidualConstant Cg CE CQ b (n/2+2) q N) * R ^ (-separationExponent) *
          Real.sqrt (R ^ (-((1 + samplingSlack - fineExponent) / 4)*(N : ℝ)) +
            (R / R ^ fineExponent)^q) ≤ R ^ (-accuracy) := by
  obtain ⟨N,q,hN,hq,hprecision⟩ := exists_source_iteration_precision accuracy
  refine ⟨N,q,hN,hq,?_⟩
  intro Cg CE CQ hCg hCE hCQ b c₀ Ca ρ hb hρ
  let ω := (1 + samplingSlack - fineExponent) / 4
  let D := fun s ↦ ∑ k ∈ Finset.range (N+1), sourceIterateProfile Cg CE CQ k s
  have hβ : ω < separationExponent := (source_iteration_fixed_gaps n).2.2.1
  have hsmall₁ := eventually_mul_rpow_le_of_exponent_lt (2*Ca)
    (show -ρ < -ω by dsimp only [ω]; linarith)
  have hsmall₂ := eventually_mul_rpow_le_of_exponent_lt (4*c₀*D (n/2+2))
    (show -separationExponent < -ω by linarith)
  have hsmall : ∀ᶠ R : ℝ in Filter.atTop,
      Ca * R ^ (-ρ) + 2*c₀*D (n/2+2)*R ^ (-separationExponent) ≤ R ^ (-ω) := by
    filter_upwards [hsmall₁,hsmall₂] with R h₁ h₂
    nlinarith only [h₁,h₂]
  obtain ⟨S₀,hS₀⟩ := Filter.eventually_atTop.mp hsmall
  have hC : 0 ≤ 2 * fourierInterpolationConstant n 1 (n/2+2) *
      finiteSourceResidualConstant Cg CE CQ b (n/2+2) q N :=
    mul_nonneg (mul_nonneg (by norm_num) (fourierInterpolationConstant_nonneg _ _ _))
      (finiteSourceResidualConstant_nonneg Cg CE CQ hCg hCE hCQ hb _ _ _)
  obtain ⟨S₁,hS₁,hfinal⟩ := hprecision _ hC
  refine ⟨max S₀ S₁,hS₁.trans (le_max_right _ _),?_⟩
  intro R hR
  exact ⟨hS₀ R ((le_max_left _ _).trans hR),hfinal R ((le_max_right _ _).trans hR)⟩

end JanetCartan.PhysicalMean
end
