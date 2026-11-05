module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.CoordinateLocalizers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Adjoints

/-!
# The selected physical sum with one identity defect

The literal physical plus pairing commutes with the selected coordinate
permutations. The full finite error subtracts the identity only once; a sum
of chartwise complete errors has an additional diagonal contribution. These
identities identify the operators for the chartwise `CompleteFactor` estimates
in `app:ch_regular:lem:finite-chain`, including their literal adjoints.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector.FiniteEvolution RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Realization CharacteristicTransport.CompleteResidual
open ResidualLocalization
variable {d q : ℕ}
local notation "H" => SpacetimeL2 d q

/-- The actual selected physical permutation commutes with conjugation of
Lebesgue L² representatives (`app:ch_regular_base:eq:signed-physical-normalization`). -/
theorem physicalPullbackL2_star (i : Fin (d + 1)) (u : H) :
    physicalPullbackL2 i (star u) = star (physicalPullbackL2 i u) := by
  apply Lp.ext
  have hs := (RegularSector.Characteristic.ResidualCoordinates.measurePreserving_physicalCoordinates i).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_star u)
  filter_upwards [physicalPullbackL2_coeFn i (star u), physicalPullbackL2_coeFn i u,
    Lp.coeFn_star (physicalPullbackL2 i u), hs] with x hx hy hz hsx
  simp only [Function.comp_apply, Pi.star_apply] at hx hy hz hsx ⊢
  exact hx.trans (hsx.trans (by rw [hz, hy]))

private theorem physicalPullbackL2_symm_star (i : Fin (d + 1)) (u : H) :
    (physicalPullbackL2 i).symm (star u) = star ((physicalPullbackL2 i).symm u) := by
  apply (physicalPullbackL2 i).injective
  rw [LinearIsometryEquiv.apply_symm_apply, physicalPullbackL2_star,
    LinearIsometryEquiv.apply_symm_apply]

/-- Coordinate transport preserves the conjugate of the whole factor; it
does not commute a Fourier multiplier through a physical cutoff
(`app:ch_regular_base:eq:signed-physical-normalization`). -/
theorem physicalOperator_boundedConjugate (i : Fin (d + 1)) (T : H →L[ℂ] H) :
    physicalOperator i (boundedConjugate T) = boundedConjugate (physicalOperator i T) := by
  ext1 u
  change (physicalPullbackL2 i).symm (star (T (star (physicalPullbackL2 i u)))) =
    star ((physicalPullbackL2 i).symm (T (physicalPullbackL2 i (star u))))
  rw [physicalPullbackL2_star, physicalPullbackL2_symm_star]

/-- The physical plus pairing of the selected finite sum is the finite sum
of its physically transported plus pairs (`app:ch_regular:eq:chain-tail`). -/
theorem physicalPair_finitePhysicalOperator {α : Type*} [Fintype α]
    (index : α → Fin (d + 1)) (T : α → H →L[ℂ] H) :
    finitePhysicalOperator index T + boundedConjugate (finitePhysicalOperator index T) =
      finitePhysicalOperator index (fun p ↦ T p + boundedConjugate (T p)) := by
  classical
  have hc : boundedConjugate (finitePhysicalOperator index T) =
      ∑ p, boundedConjugate (physicalOperator (index p) (T p)) := by
    ext1 u
    change star ((∑ p, physicalOperator (index p) (T p)) (star u)) =
      (∑ p, boundedConjugate (physicalOperator (index p) (T p))) u
    simp only [sum_apply, star_sum]
    rfl
  calc
    _ = (∑ p, physicalOperator (index p) (T p)) +
        ∑ p, boundedConjugate (physicalOperator (index p) (T p)) :=
      congrArg (fun A : H →L[ℂ] H ↦ finitePhysicalOperator index T + A) hc
    _ = ∑ p, (physicalOperator (index p) (T p) +
        boundedConjugate (physicalOperator (index p) (T p))) :=
      (Finset.sum_add_distrib ..).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← physicalOperator_boundedConjugate (index p) (T p)]
      ext1 v
      simp only [physicalOperator_apply, add_apply, map_add]

/-- Splitting into chartwise complete errors must restore `card α - 1`
identities. This is the exact diagonal term to be bounded, not discarded
(`app:ch_regular_base:eq:energy-complete-residual`, `app:ch_regular:eq:chain-tail`). -/
theorem finitePhysicalPair_sub_one_eq_chart_errors {α : Type*} [Fintype α]
    (index : α → Fin (d + 1)) (T : α → H →L[ℂ] H) :
    finitePhysicalOperator index T + boundedConjugate (finitePhysicalOperator index T) - 1 =
      finitePhysicalOperator index (fun p ↦ T p + boundedConjugate (T p) - 1) +
        ((Fintype.card α : ℝ) - 1) • (1 : H →L[ℂ] H) := by
  classical
  calc
    _ = finitePhysicalOperator index (fun p ↦ T p + boundedConjugate (T p)) - 1 :=
      congrArg (fun A : H →L[ℂ] H ↦ A - 1) (physicalPair_finitePhysicalOperator index T)
    _ = _ := by
      ext1 u
      simp only [finitePhysicalOperator, sum_apply, sub_apply, add_apply, one_apply_eq_self,
        smul_apply, physicalOperator_apply, map_sub,
        LinearIsometryEquiv.symm_apply_apply, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, sub_smul, one_smul]
      abel

/-- The same decomposition for the literal adjoint, with the one identity
subtraction unchanged (`app:ch_regular_base:eq:measured-adjoint`). -/
theorem oriented_finitePhysicalPair_sub_one_eq_chart_errors {α : Type*} [Fintype α]
    (index : α → Fin (d + 1)) (T : α → H →L[ℂ] H) (backward : Bool) :
    (if backward then
        (finitePhysicalOperator index T + boundedConjugate (finitePhysicalOperator index T) - 1).adjoint
      else finitePhysicalOperator index T + boundedConjugate (finitePhysicalOperator index T) - 1) =
      finitePhysicalOperator index (fun p ↦
        if backward then (T p + boundedConjugate (T p) - 1).adjoint
        else T p + boundedConjugate (T p) - 1) +
        ((Fintype.card α : ℝ) - 1) • (1 : H →L[ℂ] H) := by
  cases backward
  · exact finitePhysicalPair_sub_one_eq_chart_errors index T
  · simp only [ite_true, map_sub, map_add, ContinuousLinearMap.adjoint_one,
      boundedConjugate_adjoint, finitePhysicalOperator_adjoint]
    exact finitePhysicalPair_sub_one_eq_chart_errors index (fun p ↦ (T p).adjoint)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
