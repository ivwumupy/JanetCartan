module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Algebra
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.Reality

/-!
# Fixed fiber maps on genuine restriction Sobolev spaces

Weak jets, rather than an assumed multiplier estimate, supply the cost of
complex scalar multiplication, conjugation, real inclusion and real part.
Consumers are the physical plus-paired complete direct factors of
`app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped NNReal ENNReal JanetCartan.RegularSector.Realization
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
open LocalSobolev ResponseTransfer

variable {n : ℕ} {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- A fixed continuous real fiber map preserves genuine weak extensions and
bounds their infimum norm. This supplies the fixed quadrature maps used in
`app:ch_regular:eq:chain-tail`. -/
theorem compLp_restrictionSobolev_bound (L : F →L[ℝ] G)
    {U : Set (EuclideanSpace ℝ (Fin n))} {s : ℕ} {u : LocalL2 U F}
    (hu : MemRestrictionSobolev U s u) :
    MemRestrictionSobolev U s (L.compLp u) ∧
      restrictionSobolevNorm U s (L.compLp u) ≤ (‖L‖ + 1) * restrictionSobolevNorm U s u := by
  refine ⟨⟨hu.some.mapCLM L⟩, ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  have hK : 0 < ‖L‖ + 1 := by positivity
  obtain ⟨e, he⟩ := exists_extension_jetNorm_lt hu
    (lt_add_of_pos_right _ (div_pos hε hK))
  have hb := (restrictionSobolevNorm_le (e.mapCLM L)).trans (e.jetNorm_mapCLM_le L)
  have hb' := hb.trans (mul_le_mul_of_nonneg_right (by linarith : ‖L‖ ≤ ‖L‖+1)
    e.jetNorm_nonneg)
  have he' := mul_lt_mul_of_pos_left he hK
  rw [mul_add, mul_div_cancel₀ _ hK.ne'] at he'
  exact hb'.trans he'.le

/-- Fixed fiber maps have zero polynomial exponent, uniformly in every
frequency and datum (`app:ch_regular:lem:finite-chain`). -/
theorem compLp_hasPolynomialRestrictionCost {ι : Type*} (ρ : ι → ℝ)
    (L : F →L[ℝ] G) (U : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U) :
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U G hU) ρ
      (fun _ ↦ (L.compLpL 2 (volume.restrict U)).toLinearMap) := by
  intro s
  refine ⟨s, 0, ‖L‖+1, by positivity, ?_⟩
  intro i u hu
  obtain ⟨hm, hn⟩ := compLp_restrictionSobolev_bound L hu
  refine ⟨hm, ?_⟩
  change (restrictionSobolevScale U G hU).gradeNorm s (L.compLp u) ≤ _
  rw [restrictionSobolevScale_gradeNorm hU hm, restrictionSobolevScale_gradeNorm hU hu]
  simpa only [Real.rpow_zero, mul_one] using hn

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
