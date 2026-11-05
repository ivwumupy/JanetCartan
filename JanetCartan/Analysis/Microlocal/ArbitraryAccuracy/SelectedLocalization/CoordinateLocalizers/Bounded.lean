module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.CoordinateLocalizers.Integrals
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OperatorUniqueness

/-!
# Covariance of the same bounded proof localizers

The hypotheses are precisely the representative identities supplied by
`exists_bounded_physicalLocalizers`, not quantization covariance. The conclusion
identifies those same bounded maps after physical conjugation. The composed
identities feed the `CompleteFactor` and `FiniteCosts` applications to
`selectedFinite_solver_and_completeError_eq_chart_factors`.
Sources: `app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FiniteChain.Graph ProtectedMasks
open RegularSector.Characteristic RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.EvolutionIntegral RegularSector.FiniteEvolution
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q

private theorem graphOperator_input_congr
    (S : E → E → ℝ) (A : FullAmplitude (d + 1) q)
    {f g : E → Fin q → ℂ} (h : f =ᵐ[volume] g) (x : E) :
    graphOperator S A f x = graphOperator S A g x := by
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

/-- The literal bounded right realization transports to the same physical
right localizer (`app:ch_regular:eq:chain-tail`). -/
theorem physicalOperator_rightLocalizer
    (i : Fin (d + 1)) (ρ : ℝ) (m : LocalizerSymbol (d + 1))
    (R Ri : H →L[ℂ] H)
    (hR : ∀ u : H, R u =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ m (fun y ↦ (u y).ofLp) x))
    (hRi : ∀ u : H, Ri u =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ (canonicalProofLocalizer (coordinateSplit i) m)
        (fun y ↦ (u y).ofLp) x)) :
    physicalOperator i Ri = R := by
  ext1 u
  apply (physicalPullbackL2 i).injective
  simp only [physicalOperator_apply, LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  have hu := physicalPullbackL2_coeFn i u
  have hinput : (fun y ↦ (physicalPullbackL2 i u y).ofLp) =ᵐ[volume]
      (fun y ↦ (u y).ofLp) ∘ physicalCoordinates i :=
    hu.fun_comp (fun v ↦ v.ofLp)
  have he : Ri (physicalPullbackL2 i u) =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ m (fun y ↦ (u y).ofLp) (physicalCoordinates i x)) := by
    refine (hRi _).trans (.of_forall fun x ↦ ?_)
    apply congrArg (WithLp.toLp 2)
    exact (graphOperator_input_congr _ _ hinput x).trans
      (rightLocalizer_physicalCoordinates i ρ m (fun y ↦ (u y).ofLp) x)
  exact he.trans (((measurePreserving_physicalCoordinates i).quasiMeasurePreserving.ae_eq_comp
    (hR u)).symm.trans (physicalPullbackL2_coeFn i (R u)).symm)

/-- The bounded left realization is identified on integrable inputs and
then by density. No commutation of source and Fourier multipliers occurs
(`app:ch_regular:eq:chain-tail`). -/
theorem physicalOperator_leftLocalizer
    (i : Fin (d + 1)) (ρ : ℝ) (m : LocalizerSymbol (d + 1))
    (L Li : H →L[ℂ] H)
    (hL : ∀ u : H, (∀ a, Integrable (fun y ↦ u y a)) →
      L u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (leftLocalizer ρ m (fun y ↦ (u y).ofLp) x))
    (hLi : ∀ u : H, (∀ a, Integrable (fun y ↦ u y a)) →
      Li u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (leftLocalizer ρ (canonicalProofLocalizer (coordinateSplit i) m)
          (fun y ↦ (u y).ofLp) x)) :
    physicalOperator i Li = L := by
  apply EvolutionIntegratedLocalization.eq_of_leftLocalizer_representatives ρ m _ L ?_ hL
  intro u hu
  have hpull := physicalPullbackL2_coeFn i u
  have hint (a : Fin q) : Integrable (fun y ↦ physicalPullbackL2 i u y a) := by
    apply (((measurePreserving_physicalCoordinates i).integrable_comp (hu a).aestronglyMeasurable).mpr (hu a)).congr
    exact (hpull.fun_comp (fun v ↦ v a)).symm
  have hinput : (fun y ↦ (physicalPullbackL2 i u y).ofLp) =ᵐ[volume]
      (fun y ↦ (u y).ofLp) ∘ physicalCoordinates i :=
    hpull.fun_comp (fun v ↦ v.ofLp)
  have he : Li (physicalPullbackL2 i u) =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (leftLocalizer ρ m (fun y ↦ (u y).ofLp) (physicalCoordinates i x)) := by
    refine (hLi _ hint).trans (.of_forall fun x ↦ ?_)
    apply congrArg (WithLp.toLp 2)
    exact (graphOperator_input_congr _ _ hinput x).trans
      (leftLocalizer_physicalCoordinates i ρ m (fun y ↦ (u y).ofLp) x)
  rw [physicalOperator_apply]
  refine (physicalPullbackL2_symm_coeFn i (Li (physicalPullbackL2 i u))).trans ?_
  have h := ((measurePreserving_physicalCoordinates i).symm
    (physicalCoordinates i).toHomeomorph.toMeasurableEquiv).quasiMeasurePreserving.ae_eq_comp he
  change (fun x ↦ Li (physicalPullbackL2 i u) ((physicalCoordinates i).symm x)) =ᵐ[volume]
    (fun x ↦ WithLp.toLp 2 (leftLocalizer ρ m (fun y ↦ (u y).ofLp)
      (physicalCoordinates i ((physicalCoordinates i).symm x)))) at h
  simpa only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using h

/-- Exact transport of the discarded output, in its original order. The
two identifications are supplied by `physicalOperator_leftLocalizer` and
`physicalOperator_rightLocalizer` (`app:ch_regular:eq:chain-tail`). -/
theorem physicalOperator_localized_eq
    (i : Fin (d + 1)) (T L R Li Ri : H →L[ℂ] H)
    (hL : physicalOperator i Li = L) (hR : physicalOperator i Ri = R) :
    (1 - L).comp ((physicalOperator i T).comp R) =
      physicalOperator i ((1 - Li).comp (T.comp Ri)) := by
  rw [← hL, ← hR]
  ext1 u
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    one_apply_eq_self, physicalOperator_apply, map_sub,
    LinearIsometryEquiv.apply_symm_apply]

/-- The same localized identity for the literal Hilbert adjoint. Input
and output localizers stay in their specified positions
(`app:ch_regular:lem:finite-chain`). -/
theorem physicalOperator_localized_adjoint_eq
    (i : Fin (d + 1)) (T L R Li Ri : H →L[ℂ] H)
    (hL : physicalOperator i Li = L) (hR : physicalOperator i Ri = R) :
    (1 - L).comp ((physicalOperator i T).adjoint.comp R) =
      physicalOperator i ((1 - Li).comp (T.adjoint.comp Ri)) := by
  rw [physicalOperator_adjoint]
  exact physicalOperator_localized_eq i T.adjoint L R Li Ri hL hR

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
