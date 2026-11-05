module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.CrossRestriction
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Support

/-!
# The boundary discrepancy in a locally composed residual

The complete residual has the form `A - 1`, where the two physical sides of
`A` lie in the measured domain. Restricting between factors leaves a genuine
boundary term. This module identifies it without any Sobolev assertion about
zero extension. Consumer: the local factor estimate for
`app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FourierIntegral.LowBounds LocalSobolev
open RegularSector.FiniteAssembly RegularSector.Characteristic.RetardedLocalization
open RegularSector.Characteristic.EvolutionIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => SpacetimeL2 d q

/-- The part discarded by restriction and zero extension, used only as an
L² operator in the boundary correction (`app:ch_regular:eq:chain-tail`). -/
def restrictionExterior {U : Set E} (hU : MeasurableSet U) : H →L[ℝ] H :=
  1 - (SmallSupport.zeroExtend hU).toContinuousLinearMap.comp (restrictL2 U)

/-- Restriction is a left inverse of the actual isometric zero extension.
Consumer: the residual composition identity (`app:ch_regular:eq:chain-tail`). -/
theorem restrictL2_zeroExtend {U : Set E} (hU : MeasurableSet U) (u : LocalL2 U F) :
    restrictL2 U (SmallSupport.zeroExtend hU u) = u := by
  apply Lp.ext
  filter_upwards [restrictL2_coeFn U (SmallSupport.zeroExtend hU u),
    ae_restrict_of_ae (SmallSupport.zeroExtend_coeFn hU u), ae_restrict_mem hU]
    with x hx hy hz
  exact hx.trans (hy.trans (indicator_of_mem hz _))

/-- The discarded part vanishes upon restriction. No boundary regularity
is asserted (`app:ch_regular:eq:chain-tail`). -/
theorem restrictL2_restrictionExterior {U : Set E} (hU : MeasurableSet U) (v : H) :
    restrictL2 U (restrictionExterior hU v) = 0 := by
  change restrictL2 U (v - SmallSupport.zeroExtend hU (restrictL2 U v)) = 0
  rw [map_sub, restrictL2_zeroExtend, sub_self]

/-- A uniform L² bound suffices for the hard restriction. The subsequent
smooth localizer, rather than the indicator, supplies all derivatives
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_restrictionExterior_le {U : Set E} (hU : MeasurableSet U) (v : H) :
    ‖restrictionExterior hU v‖ ≤ 2 * ‖v‖ := by
  change ‖v - SmallSupport.zeroExtend hU (restrictL2 U v)‖ ≤ _
  calc
    _ ≤ ‖v‖ + ‖SmallSupport.zeroExtend hU (restrictL2 U v)‖ := norm_sub_le _ _
    _ = ‖v‖ + ‖restrictL2 U v‖ := by rw [LinearIsometry.norm_map]
    _ ≤ ‖v‖ + ‖v‖ := add_le_add le_rfl
      ((restrictL2 U).le_opNorm v |>.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (norm_restrictL2_le (q := q) U) (norm_nonneg v)))
    _ = _ := by ring

/-- The exterior of a smooth multiplier supported in U vanishes. This
turns the hard boundary tail into a smooth physical cutoff tail before
estimating it (`app:ch_regular:eq:chain-tail`). -/
theorem restrictionExterior_sourceCutMultiplier {U : Set E} (hU : MeasurableSet U)
    (χ : E → ℝ) (hχ : Continuous χ) (hb : ∀ x, ‖χ x‖ ≤ 1)
    (hs : tsupport χ ⊆ U) (v : H) :
    restrictionExterior hU (sourceCutMultiplier χ hχ hb v) = 0 := by
  change sourceCutMultiplier χ hχ hb v -
    SmallSupport.zeroExtend hU (restrictL2 U (sourceCutMultiplier χ hχ hb v)) = 0
  rw [zeroExtend_restrictL2_sourceCutMultiplier hU χ hχ hb hs, sub_self]

/-- Source multiplication ignores the exterior part. This is a pointwise
support argument and does not differentiate the indicator
(`app:ch_regular:eq:chain-tail`). -/
theorem sourceCutMultiplier_zeroExtend_restrictL2 {U : Set E} (hU : MeasurableSet U)
    (χ : E → ℝ) (hχ : Continuous χ) (hb : ∀ x, ‖χ x‖ ≤ 1)
    (hs : tsupport χ ⊆ U) (v : H) :
    sourceCutMultiplier χ hχ hb (SmallSupport.zeroExtend hU (restrictL2 U v)) =
      sourceCutMultiplier χ hχ hb v := by
  apply Lp.ext
  have hr := (ae_restrict_iff' hU).mp (restrictL2_coeFn U v)
  filter_upwards [sourceCutMultiplier_coeFn χ hχ hb
    (SmallSupport.zeroExtend hU (restrictL2 U v)), sourceCutMultiplier_coeFn χ hχ hb v,
    SmallSupport.zeroExtend_coeFn hU (restrictL2 U v), hr] with x hx hy hz hr
  rw [hx, hy, hz]
  by_cases h : x ∈ U
  · rw [indicator_of_mem h, hr h]
  · rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ h (hs hh))]
    simp

/-- The exact discrepancy for a two-sided supported `A - I`. The hypotheses
are support identities, subsequently proved for the selected complete error
from its physical masks and retained realizations. The nonzero correction
keeps its sign and the literal left/right order
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem local_residual_factor_eq_sub_boundary
    {U : Set E} (hU : MeasurableSet U) (A R Lout : H →L[ℂ] H)
    (hi : ∀ v, A (SmallSupport.zeroExtend hU (restrictL2 U v)) = A v)
    (ho : ∀ v, SmallSupport.zeroExtend hU (restrictL2 U (A v)) = A v)
    (u : LocalL2 U F) :
    (1 - localRetardedOperator hU U Lout)
        (localRetardedOperator hU U (A - 1) (localRetardedOperator hU U R u)) =
      restrictL2 U ((1 - Lout) ((A - 1) (R (SmallSupport.zeroExtend hU u)))) -
        restrictL2 U (Lout (restrictionExterior hU (R (SmallSupport.zeroExtend hU u)))) := by
  let v := R (SmallSupport.zeroExtend hU u)
  change restrictL2 U (A (SmallSupport.zeroExtend hU (restrictL2 U v)) -
      SmallSupport.zeroExtend hU (restrictL2 U v)) -
    restrictL2 U (Lout (SmallSupport.zeroExtend hU (restrictL2 U
      (A (SmallSupport.zeroExtend hU (restrictL2 U v)) -
        SmallSupport.zeroExtend hU (restrictL2 U v))))) =
      restrictL2 U ((A v - v) - Lout (A v - v)) -
        restrictL2 U (Lout (v - SmallSupport.zeroExtend hU (restrictL2 U v)))
  simp only [hi, map_sub, restrictL2_zeroExtend, ho]
  abel

/-- Physical support masks produce both hypotheses of the discrepancy
identity. The analytic estimates never need to assume this local identity
(`app:ch_regular:eq:chain-tail`). -/
theorem supported_operator_restriction_identities
    {U : Set E} (hU : MeasurableSet U) (A : H →L[ℂ] H)
    (χ ψ : E → ℝ) (hχ : Continuous χ) (hψ : Continuous ψ)
    (hχb : ∀ x, ‖χ x‖ ≤ 1) (hψb : ∀ x, ‖ψ x‖ ≤ 1)
    (hχs : tsupport χ ⊆ U) (hψs : tsupport ψ ⊆ U)
    (hi : A.comp (sourceCutMultiplier χ hχ hχb) = A)
    (ho : (sourceCutMultiplier ψ hψ hψb).comp A = A) :
    (∀ v, A (SmallSupport.zeroExtend hU (restrictL2 U v)) = A v) ∧
      (∀ v, SmallSupport.zeroExtend hU (restrictL2 U (A v)) = A v) := by
  constructor
  · intro v
    calc
      _ = A (sourceCutMultiplier χ hχ hχb
          (SmallSupport.zeroExtend hU (restrictL2 U v))) :=
        (congrArg (fun T : H →L[ℂ] H ↦ T
          (SmallSupport.zeroExtend hU (restrictL2 U v))) hi).symm
      _ = A (sourceCutMultiplier χ hχ hχb v) := by
        rw [sourceCutMultiplier_zeroExtend_restrictL2 hU χ hχ hχb hχs]
      _ = _ := congrArg (fun T : H →L[ℂ] H ↦ T v) hi
  · intro v
    apply zeroExtend_restrictL2_of_mask hU ψ hψ hψb hψs
    exact congrArg (fun T : H →L[ℂ] H ↦ T v) ho

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
