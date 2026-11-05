module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.CoordinateLocalizers.Bounded
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.CoordinateLocalizers.Restriction

/-!
# Selected-coordinate proof localizers and leakage bounds

The canonical masks are the existing `ProtectedMasks.canonicalProofLocalizer`.
Their literal integral formulas prove covariance of their bounded realizations;
the original order `(1-L) T R` and literal Hilbert adjoints are retained.
Fourier bounds transport with their exact constants. Genuine restriction bounds
use the existing weak-extension/Fourier comparisons, with a dimension/order
constant uniform over the finite coordinate index and every accuracy.

Consumer: `selectedFinite_solver_and_completeError_eq_chart_factors`, when
applying `ResidualLocalization.CompleteFactor` and `FiniteCosts`. The chart
bounds, actual finite-family grades, geometry, physical pairing and chain
assembly remain with their producers. These are coordinate deductions, not an
unconditional existence theorem. Sources: `app:ch_regular:lem:finite-chain`
and `app:ch_regular:eq:chain-tail` in `paper.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open LocalSobolev Pseudodifferential
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.RetardedLocalization RegularSector.FiniteEvolution
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q
local notation "F" => EuclideanSpace ℂ (Fin q)

/-- Both orientations retain the same physical proof masks and the literal
adjoint (`app:ch_regular:lem:finite-chain`). The identifications are proved
from the realization identities in `physicalOperator_leftLocalizer` and
`physicalOperator_rightLocalizer`. -/
theorem physicalOperator_localized_oriented_eq
    (i : Fin (d + 1)) (T L R Li Ri : H →L[ℂ] H)
    (hL : physicalOperator i Li = L) (hR : physicalOperator i Ri = R)
    (backward : Bool) :
    (1 - L).comp
      ((if backward then (physicalOperator i T).adjoint else physicalOperator i T).comp R) =
      physicalOperator i
        ((1 - Li).comp ((if backward then T.adjoint else T).comp Ri)) := by
  cases backward
  · exact physicalOperator_localized_eq i T L R Li Ri hL hR
  · exact physicalOperator_localized_adjoint_eq i T L R Li Ri hL hR

/-- Chart leakage in the actual Fourier scale transfers with exactly the
same constant, for either literal orientation. The per-chart premise is
supplied by the factor localization producer (`app:ch_regular:eq:chain-tail`). -/
theorem localized_physicalOperator_fourier_bound
    (i : Fin (d + 1)) (T L R Li Ri : H →L[ℂ] H)
    (hL : physicalOperator i Li = L) (hR : physicalOperator i Ri = R)
    (backward : Bool) (s C : ℝ)
    (hT : ∀ u, MemVectorFourierSobolev s
        ((1 - Li) ((if backward then T.adjoint else T) (Ri u))) ∧
      vectorFourierSobolevNorm s
        ((1 - Li) ((if backward then T.adjoint else T) (Ri u))) ≤ C * ‖u‖)
    (u : H) :
    MemVectorFourierSobolev s
      ((1 - L) ((if backward then (physicalOperator i T).adjoint
        else physicalOperator i T) (R u))) ∧
    vectorFourierSobolevNorm s
      ((1 - L) ((if backward then (physicalOperator i T).adjoint
        else physicalOperator i T) (R u))) ≤ C * ‖u‖ := by
  have hb := physicalOperator_signed_bound i
    ((1 - Li).comp ((if backward then T.adjoint else T).comp Ri)) 0 s C
    (by simpa only [ContinuousLinearMap.comp_apply, vectorFourierSobolevNorm_zero] using hT) u
  rw [← physicalOperator_localized_oriented_eq i T L R Li Ri hL hR backward] at hb
  simpa only [ContinuousLinearMap.comp_apply, vectorFourierSobolevNorm_zero] using hb

/-- Restriction leakage on the physical domain from the exact chart-domain
estimate returned by `CompleteFactor`. The single comparison constant depends
only on dimension, fiber size and output order, before choosing coordinates,
operators, masks, domains or accuracy (`app:ch_regular:eq:chain-tail`). -/
theorem exists_localized_physicalOperator_restriction_constant (d q m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (i : Fin (d + 1))
      (T L R Li Ri : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q),
      physicalOperator i Li = L → physicalOperator i Ri = R →
      ∀ (backward : Bool) (U : Set (Euclidean (d + 1))) (hU : MeasurableSet U) (C : ℝ),
      (∀ u, restrictL2 (physicalCoordinates i ⁻¹' U)
          ((1 - Li) ((if backward then T.adjoint else T) (Ri u))) ∈
        (restrictionSobolevScale (physicalCoordinates i ⁻¹' U) (EuclideanSpace ℂ (Fin q))
          (hU.preimage (physicalCoordinates i).continuous.measurable)).level m ∧
        (restrictionSobolevScale (physicalCoordinates i ⁻¹' U) (EuclideanSpace ℂ (Fin q))
          (hU.preimage (physicalCoordinates i).continuous.measurable)).gradeNorm m
          (restrictL2 (physicalCoordinates i ⁻¹' U)
            ((1 - Li) ((if backward then T.adjoint else T) (Ri u)))) ≤ C * ‖u‖) →
      ∀ u, restrictL2 U
          ((1 - L) ((if backward then (physicalOperator i T).adjoint
            else physicalOperator i T) (R u))) ∈
        (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).level m ∧
        (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).gradeNorm m
          (restrictL2 U ((1 - L) ((if backward then (physicalOperator i T).adjoint
            else physicalOperator i T) (R u)))) ≤ (D * C) * ‖u‖ := by
  obtain ⟨D, hD, htransport⟩ := exists_physicalOperator_restriction_transport_constant d q m
  refine ⟨D, hD, ?_⟩
  intro i T L R Li Ri hL hR backward U hU C hT u
  have hchart (v : SpacetimeL2 d q) := hT v
  simp only [restrictionSobolevScale_gradeNorm
    (hU.preimage (physicalCoordinates i).continuous.measurable) (hchart _).1] at hchart
  obtain ⟨hm, hn⟩ := htransport i
    ((1 - Li).comp ((if backward then T.adjoint else T).comp Ri)) U hU C hchart u
  rw [← physicalOperator_localized_oriented_eq i T L R Li Ri hL hR backward] at hm hn
  exact ⟨hm, (restrictionSobolevScale_gradeNorm hU hm).le.trans hn⟩

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
