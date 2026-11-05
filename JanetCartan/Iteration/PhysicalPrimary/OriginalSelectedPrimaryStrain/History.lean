module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledPolynomial
public import JanetCartan.Iteration.PhysicalMean.FixedPicardPrecisionSelection

/-!
# The ordinary primary carrier in the original observed-chain family

The source in `main:eq:primary-strain` has the undoubled frequency
`R ^ carrierExponent` and raw amplitude scale `R`. Unlike a signed difference,
it has no mesh-dependent beat. The numerical admission below keeps the original
history and both original thresholds; it chooses neither a source nor a mask.
The consumer is the same-history observed source residual.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain

open OriginalHistoryFamily PhysicalInitialization.OriginalSampledPolynomial

/-- The true raw-primary scale already lies in the original fixed exponent
window. No accuracy-dependent initial threshold is needed. -/
theorem primary_frequency_window {R : ℝ} (hR : 1 ≤ R) :
    1 ≤ R ^ carrierExponent ∧ R ≤ (R ^ carrierExponent) ^ (1 - (1 / 1000 : ℝ)) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  refine ⟨Real.one_le_rpow hR (by norm_num [carrierExponent]), ?_⟩
  rw [← Real.rpow_mul hRp.le]
  calc
    R = R ^ (1 : ℝ) := (Real.rpow_one R).symm
    _ ≤ R ^ (carrierExponent * (1 - (1 / 1000 : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le hR (by norm_num [carrierExponent])

/-- Insert the unchanged physical history at the ordinary carrier, with
unit operator normalization and the genuine raw-amplitude scale. -/
def primaryHistory {d : ℕ} {B : ℝ} {kMin : ℕ} {Sreg Sop R₀ : ℝ}
    (hR₀ : 2 ≤ R₀) (hreg : Sreg ≤ R₀) (hop : Sop ≤ R₀)
    (j : ℕ)
    (u : Fin j → SchwartzMap (Euclidean (d+1)) (Euclidean (embeddingDimension (d+1))))
    (ell : Fin j → ℕ) (hu : RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell) :
    Histories d B kMin Sreg Sop := by
  let R := historyScale R₀ growthExponent j
  have facts := PhysicalMean.fixedPicard_history_scale_facts hR₀ j
  have window := primary_frequency_window facts.1
  exact ⟨⟨R₀,j,u,ell,R ^ carrierExponent,R,1,()⟩,
    max_le hreg hop,hu,window.1,facts.2.2.1,window.2,zero_le_one⟩

/-- The admitted operator label retains the exact original current scale,
frequency and every increment of the supplied finite history. -/
theorem primaryHistory_values {d : ℕ} {B : ℝ} {kMin : ℕ} {Sreg Sop R₀ : ℝ}
    (hR₀ : 2 ≤ R₀) (hreg : Sreg ≤ R₀) (hop : Sop ≤ R₀)
    (j : ℕ)
    (u : Fin j → SchwartzMap (Euclidean (d+1)) (Euclidean (embeddingDimension (d+1))))
    (ell : Fin j → ℕ) (hu : RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell) :
    (primaryHistory hR₀ hreg hop j u ell hu).val.lam =
        (historyScale R₀ growthExponent j) ^ carrierExponent ∧
      (primaryHistory hR₀ hreg hop j u ell hu).val.K =
        historyScale R₀ growthExponent j ∧
      (primaryHistory hR₀ hreg hop j u ell hu).val.u = u := by
  exact ⟨rfl,rfl,rfl⟩

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
end
