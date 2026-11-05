module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Positive
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.CommonMasks

/-!
# Literal measured masks and zero extension

The outer masks themselves supply support for `measured-adjoint` and
`negative-duality`. No plateau identity for either mask is required.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set
namespace JanetCartan.RegularSector.FiniteAssembly
open LocalSobolev FourierIntegral.LowBounds Characteristic.RetardedLocalization
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

/-- Literal localization in `app:ch_regular_base:eq:measured-adjoint`.
The source mask remains to the right of the original direct residual. -/
def measuredOperator (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (sourceCutMultiplier χout ho hob).comp (T.comp (sourceCutMultiplier χin hi hib))

/-- The literal Hilbert adjoint exchanges the real masks, without moving
one through T (`app:ch_regular_base:eq:measured-adjoint`). -/
theorem measuredOperator_adjoint
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1) (T : H →L[ℂ] H) :
    (measuredOperator χout χin ho hi hob hib T).adjoint =
      measuredOperator χin χout hi ho hib hob T.adjoint := by
  simp only [measuredOperator, ContinuousLinearMap.adjoint_comp,
    sourceCutMultiplier_adjoint, ContinuousLinearMap.comp_assoc]

/-- A mask supported in the measured domain identifies its output with the
zero extension of its restriction (`app:ch_regular_base:eq:negative-duality`). -/
theorem zeroExtend_restrictL2_sourceCutMultiplier
    {V : Set E} (hV : MeasurableSet V) (χ : E → ℝ) (hχ : Continuous χ)
    (hb : ∀ y, ‖χ y‖ ≤ 1) (hs : tsupport χ ⊆ V) (u : H) :
    SmallSupport.zeroExtend hV (restrictL2 V (sourceCutMultiplier χ hχ hb u)) =
      sourceCutMultiplier χ hχ hb u := by
  apply Lp.ext
  have hr := (ae_restrict_iff' hV).mp (restrictL2_coeFn V (sourceCutMultiplier χ hχ hb u))
  filter_upwards [SmallSupport.zeroExtend_coeFn hV
    (restrictL2 V (sourceCutMultiplier χ hχ hb u)), hr,
    sourceCutMultiplier_coeFn χ hχ hb u] with y hy hr hm
  rw [hy]
  by_cases hyV : y ∈ V
  · exact (indicator_of_mem hyV _).trans (hr hyV)
  · rw [indicator_of_notMem hyV, hm]
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hyV (hs h))]
    simp

/-- The actual local measured output has its original global zero extension.
Consumer: the supported negative norm in `negative-duality`. -/
theorem zeroExtend_local_measuredOperator
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1)
    (hs : tsupport χout ⊆ V) (T : H →L[ℂ] H) (u : LocalL2 U F) :
    SmallSupport.zeroExtend hV
        (localRetardedOperator hU V (measuredOperator χout χin ho hi hob hib T) u) =
      measuredOperator χout χin ho hi hob hib T (SmallSupport.zeroExtend hU u) :=
  zeroExtend_restrictL2_sourceCutMultiplier hV χout ho hob hs _

/-- The adjoint on the original local spaces literally exchanges the domains
and masks (`app:ch_regular_base:eq:measured-adjoint`). -/
theorem local_measuredOperator_adjoint
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1) (T : H →L[ℂ] H) :
    (localRetardedOperator hU V (measuredOperator χout χin ho hi hob hib T)).adjoint =
      localRetardedOperator hV U (measuredOperator χin χout hi ho hib hob T.adjoint) := by
  rw [localRetardedOperator_adjoint, measuredOperator_adjoint]

/-- The literal local adjoint has the exchanged zero-extension identity,
using the source mask's actual support (`negative-duality`). -/
theorem zeroExtend_local_measuredOperator_adjoint
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1)
    (hs : tsupport χin ⊆ U) (T : H →L[ℂ] H) (v : LocalL2 V F) :
    SmallSupport.zeroExtend hU
        ((localRetardedOperator hU V (measuredOperator χout χin ho hi hob hib T)).adjoint v) =
      (measuredOperator χout χin ho hi hob hib T).adjoint (SmallSupport.zeroExtend hV v) := by
  rw [local_measuredOperator_adjoint, measuredOperator_adjoint]
  exact zeroExtend_local_measuredOperator hV hU χin χout hi ho hib hob hs T.adjoint v

end JanetCartan.RegularSector.FiniteAssembly
