module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.CrossRestriction

/-!
# Exact restriction identities for the whole-space chain

Whole-space restriction and zero extension cancel on the original L² classes.
These identities retain the literal right quantizations in the terminal step
of `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector.Characteristic.RetardedLocalization RegularSector.Characteristic.EvolutionIntegral
open LocalSobolev
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d q

/-- On the whole-space restriction measure, zero extension exactly reverses
restriction (`app:ch_regular:lem:finite-chain`). -/
theorem zeroExtend_restrictL2_univ (u : H) :
    SmallSupport.zeroExtend MeasurableSet.univ (restrictL2 univ u) = u := by
  apply Lp.ext
  have hr := (ae_restrict_iff' MeasurableSet.univ).mp (restrictL2_coeFn univ u)
  filter_upwards [SmallSupport.zeroExtend_coeFn MeasurableSet.univ (restrictL2 univ u), hr]
    with x hx hxr
  rw [hx, indicator_of_mem (mem_univ x)]
  exact hxr (mem_univ x)

/-- The actual whole-space restriction defect keeps the original two RIGHT
operators and exactly one identity (`app:ch_regular:eq:chain-tail`). -/
theorem local_univ_rightLocalizer_defect_eq (Ri Mt : H →L[ℂ] H) :
    (1-localRetardedOperator MeasurableSet.univ univ Mt).comp
      (localRetardedOperator MeasurableSet.univ univ Ri) =
    localRetardedOperator MeasurableSet.univ univ ((1-Mt).comp Ri) := by
  ext1 u
  change restrictL2 univ (Ri (SmallSupport.zeroExtend MeasurableSet.univ u)) -
      restrictL2 univ (Mt (SmallSupport.zeroExtend MeasurableSet.univ
        (restrictL2 univ (Ri (SmallSupport.zeroExtend MeasurableSet.univ u))))) =
    restrictL2 univ (Ri (SmallSupport.zeroExtend MeasurableSet.univ u) -
      Mt (Ri (SmallSupport.zeroExtend MeasurableSet.univ u)))
  rw [zeroExtend_restrictL2_univ, map_sub]

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
