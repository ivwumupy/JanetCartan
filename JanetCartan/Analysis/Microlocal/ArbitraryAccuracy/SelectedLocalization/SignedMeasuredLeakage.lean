module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SignedLetterRestriction
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.CoordinateLocalizers
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Physical

/-!
# Measured signed letters from the retained chart leakage

Transport the same measured operator through its coordinate map, external
scalar, whole conjugate and literal adjoint, then pass to the local restriction
space. The Fourier input is supplied by the measured characteristic constructor;
this deduction does not select a new solver or proof mask.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
open Set MeasureTheory
open scoped JanetCartan.RegularSector.Realization
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open ResidualLocalization LocalSobolev Pseudodifferential FourierIntegral.LowBounds
open RegularSector RegularSector.Realization RegularSector.FiniteAssembly
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.RetardedLocalization
open RegularSector.FiniteEvolution RegularSector.Characteristic.ResidualCoordinates
open RegularSector.FiniteMasks.ActualFamily RegularSector.FiniteResidual.FiniteIdentity
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => SpacetimeL2 d q

/-- The original two measurement masks pull back to their respective chart
positions. Consumer: measured characteristic leakage on the physical chain
(`app:ch_regular_base:eq:measured-adjoint`, `app:ch_regular:eq:chain-tail`). -/
theorem measuredOperator_physicalOperator_eq
    (i : Fin (d+1)) (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1) (T : H →L[ℂ] H) :
    measuredOperator μ ν hμ hν hμb hνb (physicalOperator i T) =
      physicalOperator i (measuredOperator (μ ∘ physicalCoordinates i)
        (ν ∘ physicalCoordinates i) (hμ.comp (physicalCoordinates i).continuous)
        (hν.comp (physicalCoordinates i).continuous) (fun _ ↦ hμb _) (fun _ ↦ hνb _) T) := by
  ext1 u
  apply (physicalPullbackL2 i).injective
  simp only [measuredOperator, ContinuousLinearMap.comp_apply, physicalOperator_apply,
    physicalPullbackL2_sourceCutMultiplier, LinearIsometryEquiv.apply_symm_apply]

/-- Real measurements preserve the external scalar and whole conjugate of
an individual residual letter. No real projection is inserted between factors
(`app:ch_regular_base:eq:signed-physical-normalization`). -/
theorem measuredOperator_signed_eq
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (T : H →L[ℂ] H) (z : ℂ) (reflected : Bool) :
    measuredOperator μ ν hμ hν hμb hνb
        (if reflected then boundedConjugate (z • T) else z • T) =
      if reflected then boundedConjugate (z • measuredOperator μ ν hμ hν hμb hνb T)
        else z • measuredOperator μ ν hμ hν hμb hνb T := by
  have he : measuredOperator μ ν hμ hν hμb hνb (z • T) =
      z • measuredOperator μ ν hμ hν hμb hνb T := by
    ext1 u
    simp only [measuredOperator, ContinuousLinearMap.comp_apply, smul_apply, map_smul]
  cases reflected
  · exact he
  · simpa only [← he, ite_true] using (boundedConjugate_measuredOperator μ ν hμ hν hμb hνb (z • T)).symm

/-- A measured branch's Fourier leakage gives the exact local restriction
bound for each scalar-weighted, whole-conjugated letter and its literal adjoint.
The dimension/order constant precedes every operator, mask and accuracy.
The Fourier premise is the output of the retained characteristic or elliptic
localization producer. Consumer: `finiteChain_observation_rapidDecayAt.hleak`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_signedMeasuredLetter_local_restriction_comparison (d q m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (U : Set (Euclidean (d+1))) (hU : MeasurableSet U)
      (T R Lout : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q),
      (∀ u, R (star u) = star (R u)) →
      (∀ u, Lout (star u) = star (Lout u)) →
      ∀ (μ ν : Euclidean (d+1) → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
        (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1),
      tsupport μ ⊆ U → tsupport ν ⊆ U →
      ∀ (z : ℂ) (reflected backward : Bool) (B : ℝ), 0 ≤ B →
      let A := measuredOperator μ ν hμ hν hμb hνb T
      (∀ u, MemVectorFourierSobolev (m : ℝ)
          ((1 - Lout) ((if backward then A.adjoint else A) (R u))) ∧
        vectorFourierSobolevNorm (m : ℝ)
          ((1 - Lout) ((if backward then A.adjoint else A) (R u))) ≤ B * ‖u‖) →
      let P := measuredOperator μ ν hμ hν hμb hνb
        (if reflected then boundedConjugate (z • T) else z • T)
      let S := if backward then P.adjoint else P
      ∀ u : LocalL2 U (EuclideanSpace ℂ (Fin q)),
        let v := (1 - localRetardedOperator hU U Lout)
          (localRetardedOperator hU U S (localRetardedOperator hU U R u))
        v ∈ (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).level m ∧
        (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).gradeNorm m v ≤
          K * B * ‖z‖ * ‖u‖ := by
  obtain ⟨K, hK, hb⟩ := exists_signedLetter_fourier_restriction_comparison d q m
  refine ⟨K, hK, ?_⟩
  intro U hU T R Lout hR hL μ ν hμ hν hμb hνb hμs hνs z reflected backward B hB A hbound P S u v
  have he := measuredOperator_oriented_local_leakage_eq hU
    (if reflected then boundedConjugate (z • T) else z • T) R Lout
    μ ν hμ hν hμb hνb hμs hνs backward u
  change v = _ at he
  rw [he]
  have hp := measuredOperator_signed_eq μ ν hμ hν hμb hνb T z reflected
  change P = _ at hp
  have hs : S = if backward then
      (if reflected then boundedConjugate (z • A) else z • A).adjoint
    else (if reflected then boundedConjugate (z • A) else z • A) := by
    dsimp only [S]
    rw [hp]
  change restrictL2 U ((1 - Lout) (S (R (SmallSupport.zeroExtend hU u)))) ∈ _ ∧ _
  change restrictL2 U ((1 - Lout) (S (R (SmallSupport.zeroExtend hU u)))) ∈ _ ∧
    (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).gradeNorm m
      (restrictL2 U ((1 - Lout) (S (R (SmallSupport.zeroExtend hU u))))) ≤ _
  rw [hs]
  simpa only [LinearIsometry.norm_map] using
    hb U hU A R Lout hR hL z reflected backward B hB hbound (SmallSupport.zeroExtend hU u)


/-- Apply the signed local comparison directly to the measured chart estimate
returned by `exists_finite_selected_direct_construction_with_measured_characteristic_leakage`.
The coordinate identities come from the same bounded localizer representatives,
and the even proof masks supply conjugation invariance. All measurement masks,
zero extensions, external scalars and literal adjoints are retained.
Consumer: the individual normalized characteristic letters in every mixed word
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_signedMeasuredChart_local_restriction_comparison (d q m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i : Fin (d+1))
      (U : Set (Euclidean (d+1))) (hU : MeasurableSet U)
      (T R Lout Ri Li : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q),
      physicalOperator i Ri = R → physicalOperator i Li = Lout →
      (∀ u, R (star u) = star (R u)) →
      (∀ u, Lout (star u) = star (Lout u)) →
      ∀ (μ ν : Euclidean (d+1) → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
        (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1),
      tsupport μ ⊆ U → tsupport ν ⊆ U →
      ∀ (z : ℂ) (reflected backward : Bool) (B : ℝ), 0 ≤ B →
      let A := measuredOperator (μ ∘ physicalCoordinates i) (ν ∘ physicalCoordinates i)
        (hμ.comp (physicalCoordinates i).continuous) (hν.comp (physicalCoordinates i).continuous)
        (fun _ ↦ hμb _) (fun _ ↦ hνb _) T
      (∀ u, MemVectorFourierSobolev (m : ℝ)
          ((1 - Li) ((if backward then A.adjoint else A) (Ri u))) ∧
        vectorFourierSobolevNorm (m : ℝ)
          ((1 - Li) ((if backward then A.adjoint else A) (Ri u))) ≤ B * ‖u‖) →
      let P := measuredOperator μ ν hμ hν hμb hνb
        (if reflected then boundedConjugate (z • physicalOperator i T) else z • physicalOperator i T)
      let S := if backward then P.adjoint else P
      ∀ u : LocalL2 U (EuclideanSpace ℂ (Fin q)),
        let v := (1 - localRetardedOperator hU U Lout)
          (localRetardedOperator hU U S (localRetardedOperator hU U R u))
        v ∈ (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).level m ∧
        (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).gradeNorm m v ≤
          K * B * ‖z‖ * ‖u‖ := by
  obtain ⟨K, hK, hb⟩ := exists_signedMeasuredLetter_local_restriction_comparison d q m
  refine ⟨K, hK, ?_⟩
  intro i U hU T R Lout Ri Li hRi hLi hR hL μ ν hμ hν hμb hνb hμs hνs
    z reflected backward B hB A hbound
  apply hb U hU (physicalOperator i T) R Lout hR hL μ ν hμ hν hμb hνb hμs hνs
    z reflected backward B hB
  rw [measuredOperator_physicalOperator_eq]
  exact localized_physicalOperator_fourier_bound i A Lout R Li Ri hLi hRi backward m B hbound

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
