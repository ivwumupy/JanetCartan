module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SignedWordSupport
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.WholeSpaceRestriction
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Support.Multipliers

/-!
# The original source plateau on individual measured letters

The physical measurement proves the support premise of the normalized terminal
observation. The literal adjoint exchanges the two measurements; each side uses
its own original plateau (`app:ch_regular_base:eq:measured-adjoint`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector.FiniteAssembly FourierIntegral.LowBounds LocalSobolev
open RegularSector.Characteristic.RetardedLocalization
open RegularSector.Characteristic.EvolutionIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d q

/-- The original output measurement is fixed by its supplied source plateau.
This proves the factor-support input of
`normalizedSource_finiteChain_observation_rapidDecayAt`, without imposing a
support condition on localized near chains (`app:ch_regular:lem:finite-chain`). -/
theorem measuredOperator_source_plateau
    (μ ν χ : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν) (hχ : Continuous χ)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1) (hχb : ∀ y, ‖χ y‖ ≤ 1)
    (hplateau : ∀ y ∈ tsupport μ, χ y = 1) (T : H →L[ℂ] H) (u : H) :
    sourceCutMultiplier χ hχ hχb (measuredOperator μ ν hμ hν hμb hνb T u) =
      measuredOperator μ ν hμ hν hμb hνb T u := by
  exact DFunLike.congr_fun (sourceCutMultiplier_plateau_comp μ χ hμ hχ hμb hχb hplateau).2
    (T (sourceCutMultiplier ν hν hνb u))

/-- The whole-space restriction of an oriented measured letter is fixed
by the SAME physical plateau after zero extension. The backward orientation
requires the actual input-mask plateau, exactly as dictated by the adjoint
(`app:ch_regular_base:eq:measured-adjoint`, `app:ch_regular:eq:chain-tail`). -/
theorem local_measuredOperator_oriented_source_plateau
    (μ ν χ : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν) (hχ : Continuous χ)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1) (hχb : ∀ y, ‖χ y‖ ≤ 1)
    (T : H →L[ℂ] H) (backward : Bool)
    (hplateau : ∀ y ∈ tsupport (if backward then ν else μ), χ y = 1)
    (u : LocalL2 (univ : Set E) (EuclideanSpace ℂ (Fin q))) :
    let P := measuredOperator μ ν hμ hν hμb hνb T
    let D := if backward then P.adjoint else P
    sourceCutMultiplier χ hχ hχb (SmallSupport.zeroExtend MeasurableSet.univ
      (localRetardedOperator MeasurableSet.univ univ D u)) =
      SmallSupport.zeroExtend MeasurableSet.univ
        (localRetardedOperator MeasurableSet.univ univ D u) := by
  intro P D
  change sourceCutMultiplier χ hχ hχb (SmallSupport.zeroExtend MeasurableSet.univ
    (restrictL2 univ (D (SmallSupport.zeroExtend MeasurableSet.univ u)))) =
      SmallSupport.zeroExtend MeasurableSet.univ
        (restrictL2 univ (D (SmallSupport.zeroExtend MeasurableSet.univ u)))
  rw [zeroExtend_restrictL2_univ]
  cases backward with
  | false =>
    simpa only [D, P, Bool.false_eq_true, ite_false] using
      measuredOperator_source_plateau μ ν χ hμ hν hχ hμb hνb hχb hplateau T
        (SmallSupport.zeroExtend MeasurableSet.univ u)
  | true =>
    simpa only [D, P, ite_true, measuredOperator_adjoint] using
      measuredOperator_source_plateau ν μ χ hν hμ hχ hνb hμb hχb hplateau T.adjoint
        (SmallSupport.zeroExtend MeasurableSet.univ u)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
