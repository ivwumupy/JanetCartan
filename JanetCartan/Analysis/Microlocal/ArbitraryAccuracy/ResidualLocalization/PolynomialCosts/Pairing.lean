module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.FiberMaps

/-!
# Literal physical plus pairing on restriction scales

The concrete direct-factor estimates are closed under the finite operations
used by `CompleteResidual.Reality.physicalPairedSectorSum`. In particular the
pairing is `S + cSc`, with no anti-real normalization. Fixed fiber maps use
actual weak extensions from `FiberMaps`. Sources:
`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped NNReal ENNReal JanetCartan.RegularSector.Realization
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
open LocalSobolev ResponseTransfer RegularSector RegularSector.Realization
open RegularSector.Characteristic.RetardedLocalization
open CharacteristicTransport.CompleteResidual

/-- Fixed fiber maps commute with literal zero extension, by their a.e.
representatives. Consumer: whole-factor conjugation and real compression in
`app:ch_regular:eq:chain-tail`. -/
theorem compLp_zeroExtend {n : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : MeasurableSet U) (u : LocalL2 U F) :
    L.compLp (SmallSupport.zeroExtend hU u) = SmallSupport.zeroExtend hU (L.compLp u) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (SmallSupport.zeroExtend hU u),
    SmallSupport.zeroExtend_coeFn hU u, SmallSupport.zeroExtend_coeFn hU (L.compLp u),
    (ae_restrict_iff' hU).mp (L.coeFn_compLp u)] with x hx hy hz hu
  rw [hx, hy, hz]
  by_cases hi : x ∈ U
  · simp only [indicator_of_mem hi]
    exact (hu hi).symm
  · simp [hi]

variable {d q : ℕ} {ι κ : Type*}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

private theorem restrictL2_compLp (L : F →L[ℝ] F) (U : Set E) (u : H) :
    restrictL2 U (L.compLp u) = L.compLp (restrictL2 U u) := by
  apply Lp.ext
  filter_upwards [restrictL2_coeFn U (L.compLp u), L.coeFn_compLp (restrictL2 U u),
    ae_restrict_of_ae (L.coeFn_compLp u), restrictL2_coeFn U u] with x hx hy hz hu
  rw [hx, hy, hz, hu]

private theorem compLp_conjugation {μ : Measure E} (u : Lp F 2 μ) :
    (starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap.compLp u = star u := by
  apply Lp.ext
  filter_upwards [(starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap.coeFn_compLp u,
    Lp.coeFn_star u] with x hx hy
  exact hx.trans hy.symm

/-- Whole-factor conjugation preserves the proved restriction cost. No mask
is moved through the factor (`app:ch_regular:lem:finite-chain`). -/
theorem boundedConjugate_hasPolynomialRestrictionCost
    (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (T : ι → H →L[ℂ] H)
    (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hT : HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale V F hV) ρ
      (fun i ↦ (localRetardedOperator hU V (T i)).toLinearMap)) :
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale V F hV) ρ
      (fun i ↦ (localRetardedOperator hU V (boundedConjugate (T i))).toLinearMap) := by
  let L := (starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap
  have hi := compLp_hasPolynomialRestrictionCost ρ L U hU
  have ho := compLp_hasPolynomialRestrictionCost ρ L V hV
  have hc := polynomialCost_comp _ _ _ hρ ho (polynomialCost_comp _ _ _ hρ hT hi)
  convert hc using 1
  funext i
  apply LinearMap.ext
  intro u
  change restrictL2 V (star (T i (star (SmallSupport.zeroExtend hU u)))) =
    L.compLp (restrictL2 V (T i (SmallSupport.zeroExtend hU (L.compLp u))))
  rw [← compLp_conjugation, restrictL2_compLp, ← compLp_conjugation,
    compLp_zeroExtend]

/-- Two complete masked factors can be added on the existing restriction
scale (`app:ch_regular:eq:chain-tail`). -/
theorem localOperator_add_hasPolynomialRestrictionCost
    (ρ : ι → ℝ) (hρ : ∀ i, 1 ≤ ρ i) (S T : ι → H →L[ℂ] H)
    (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hS : HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale V F hV) ρ
      (fun i ↦ (localRetardedOperator hU V (S i)).toLinearMap))
    (hT : HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale V F hV) ρ
      (fun i ↦ (localRetardedOperator hU V (T i)).toLinearMap)) :
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale V F hV) ρ
      (fun i ↦ (localRetardedOperator hU V (S i + T i)).toLinearMap) := by
  convert polynomialCost_add _ _ hρ hS hT using 1
  ext i u
  simp [localRetardedOperator]

/-- The full finite sum uses a common input order and exponent before the
family index (`app:ch_regular:lem:finite-chain`). -/
theorem localOperator_sum_hasPolynomialRestrictionCost
    (ρ : ι → ℝ) (hρ : ∀ i, 1 ≤ ρ i) (T : κ → ι → H →L[ℂ] H) (I : Finset κ)
    (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hT : ∀ j ∈ I, HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale V F hV) ρ
      (fun i ↦ (localRetardedOperator hU V (T j i)).toLinearMap)) :
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale V F hV) ρ
      (fun i ↦ (localRetardedOperator hU V (∑ j ∈ I, T j i)).toLinearMap) := by
  convert polynomialCost_sum _ _ hρ _ I hT using 1
  ext i u
  simp [localRetardedOperator, map_sum]

private theorem compLp_complex_smul {μ : Measure E} (c : ℂ) (u : Lp F 2 μ) :
    ((c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ).compLp u = c • u := by
  apply Lp.ext
  filter_upwards [((c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ).coeFn_compLp u,
    Lp.coeFn_smul c u] with x hx hy
  exact hx.trans hy.symm

/-- Fixed complex coefficients, including the literal `1/i` and its conjugate,
preserve the restriction cost (`app:ch_regular:eq:chain-tail`). -/
theorem localOperator_smul_hasPolynomialRestrictionCost
    (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (T : ι → H →L[ℂ] H) (c : ℂ)
    (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hT : HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale V F hV) ρ
      (fun i ↦ (localRetardedOperator hU V (T i)).toLinearMap)) :
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale V F hV) ρ
      (fun i ↦ (localRetardedOperator hU V (c • T i)).toLinearMap) := by
  let L := (c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ
  have ho := compLp_hasPolynomialRestrictionCost ρ L V hV
  convert polynomialCost_comp _ _ _ hρ ho hT using 1
  funext i
  apply LinearMap.ext
  intro u
  change restrictL2 V (c • T i (SmallSupport.zeroExtend hU u)) =
    L.compLp (restrictL2 V (T i (SmallSupport.zeroExtend hU u)))
  rw [← compLp_complex_smul, restrictL2_compLp]

/-- Retaining the full identity defect costs no additional input hypothesis.
The local identity is the restriction of literal whole-space identity
(`app:ch_regular:eq:chain-tail`). -/
theorem localOperator_identity_hasPolynomialRestrictionCost
    (ρ : ι → ℝ) (U : Set E) (hU : MeasurableSet U) :
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ
      (fun _ ↦ (localRetardedOperator hU U (ContinuousLinearMap.id ℂ H)).toLinearMap) := by
  have he : (localRetardedOperator hU U (ContinuousLinearMap.id ℂ H)).toLinearMap =
      LinearMap.id := by
    apply LinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [restrictL2_coeFn U (SmallSupport.zeroExtend hU u),
      ae_restrict_of_ae (SmallSupport.zeroExtend_coeFn hU u), ae_restrict_mem hU]
      with x hx hy hz
    exact hx.trans (hy.trans (indicator_of_mem hz _))
  simp only [he]
  exact polynomialCost_identity _ ρ

/-- The PHYSICAL `S+cSc` finite sum inherits the actual factors' costs.
Its producer inputs are the elapsed/PDO endpoints, assembled in `Complete`;
this structural consequence supplies neither of those analytic estimates.
Source: `app:ch_regular:eq:chain-tail` and the physical pairing in
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem physicalPairedSectorSum_hasPolynomialRestrictionCost
    (ρ : ι → ℝ) (hρ : ∀ i, 1 ≤ ρ i) (T : κ → ι → H →L[ℂ] H) (I : Finset κ)
    (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hT : ∀ j ∈ I, HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale V F hV) ρ
      (fun i ↦ (localRetardedOperator hU V (T j i)).toLinearMap)) :
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale V F hV) ρ
      (fun i ↦ (localRetardedOperator hU V
        (physicalPairedSectorSum I (fun j ↦ T j i))).toLinearMap) := by
  have hs := localOperator_sum_hasPolynomialRestrictionCost ρ hρ T I U V hU hV hT
  exact localOperator_add_hasPolynomialRestrictionCost ρ hρ _ _ U V hU hV hs
    (boundedConjugate_hasPolynomialRestrictionCost ρ (fun i ↦ zero_lt_one.trans_le (hρ i))
      _ U V hU hV hs)

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
