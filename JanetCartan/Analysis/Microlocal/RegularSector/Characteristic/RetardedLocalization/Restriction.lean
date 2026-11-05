module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization.Support
public import JanetCartan.Analysis.Operator.RealQuadratures.RealPart

/-!
# Restricting the same retarded operator and its literal adjoint

These maps use the existing Lebesgue `LocalL2` spaces and isometric zero
extension. The local adjoint exchanges the two domains. The supported-output
identity required by the negative-duality consumer is proved from the masks.
No distribution-completion extension is asserted.
Source: `app:ch_regular_base:eq:negative-duality`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.Characteristic.RetardedLocalization
open FourierIntegral LowBounds LocalSobolev EvolutionIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => EuclideanSpace ℂ (Fin q)
local notation "H" => SpacetimeL2 d q

/-- Literal restriction to the measured domain, as a real bounded map.
Consumer: `localRetardedOperator`, with no change to the input measure. -/
def restrictL2 (U : Set E) : H →L[ℝ] LocalL2 U V :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using (Measure.restrict_le_self (μ := volume) (s := U)))

/-- The restriction map keeps the original representative almost everywhere
on its domain (`app:ch_regular_base:eq:negative-duality`). -/
theorem restrictL2_coeFn (U : Set E) (u : H) :
    restrictL2 U u =ᵐ[volume.restrict U] u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u

/-- Restriction is contractive without a domain-volume constant. -/
theorem norm_restrictL2_le (U : Set E) : ‖restrictL2 (q := q) U‖ ≤ 1 := by
  simpa only [restrictL2, ENNReal.toReal_one, Real.one_rpow] using
    (Lp.norm_LpToLpOfMeasureLeSMul_le («E» := V) (p := 2) (c := 1)
      (by simp) (by simpa only [one_smul] using
        (Measure.restrict_le_self (μ := volume) (s := U))))

/-- Restriction and the existing zero extension are literal Hilbert adjoints.
This uses the real Hilbert structure underlying the complex finite fiber. -/
theorem restrictL2_adjoint {U : Set E} (hU : MeasurableSet U) :
    (restrictL2 (q := q) U).adjoint = (SmallSupport.zeroExtend hU).toContinuousLinearMap := by
  ext1 u
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (inner_zeroExtend_eq_of_restrict hU u (restrictL2 U v) v
    (restrictL2_coeFn U v).symm).symm

/-- The reverse adjoint is the same restriction, not a new extension. -/
theorem zeroExtend_adjoint {U : Set E} (hU : MeasurableSet U) :
    ((SmallSupport.zeroExtend (F := V) (p := 2) (μ := volume) hU).toContinuousLinearMap).adjoint =
      restrictL2 U := by
  rw [← restrictL2_adjoint hU, ContinuousLinearMap.adjoint_adjoint]

/-- The actual local operator: zero-extend its source, apply the same bounded
retarded map, then restrict to the measurement domain (`negative-duality`). -/
def localRetardedOperator {U : Set E} (hU : MeasurableSet U) (W : Set E)
    (Q : H →L[ℂ] H) : LocalL2 U V →L[ℝ] LocalL2 W V :=
  (restrictL2 W).comp ((Q.restrictScalars ℝ).comp
    (SmallSupport.zeroExtend hU).toContinuousLinearMap)

/-- The local literal adjoint exchanges the source and measurement domains
and uses the original complex Hilbert adjoint. -/
theorem localRetardedOperator_adjoint {U W : Set E}
    (hU : MeasurableSet U) (hW : MeasurableSet W) (Q : H →L[ℂ] H) :
    (localRetardedOperator hU W Q).adjoint = localRetardedOperator hW U Q.adjoint := by
  simp only [localRetardedOperator, ContinuousLinearMap.adjoint_comp,
    restrictL2_adjoint hW, zeroExtend_adjoint hU,
    adjoint_restrictScalars_complex, ContinuousLinearMap.comp_assoc]

/-- Restriction followed by zero extension recovers any output fixed by a
mask supported in the measured domain. This is a support proof, not a
positive-order Sobolev zero-extension theorem (`negative-duality`). -/
theorem zeroExtend_restrictL2_of_mask {W : Set E} (hW : MeasurableSet W)
    (ψ : E → ℝ) (hψ : Continuous ψ) (hb : ∀ x, ‖ψ x‖ ≤ 1)
    (hs : tsupport ψ ⊆ W) (u : H) (hu : sourceCutMultiplier ψ hψ hb u = u) :
    SmallSupport.zeroExtend hW (restrictL2 W u) = u := by
  apply Lp.ext
  have hr := (ae_restrict_iff' hW).mp (restrictL2_coeFn W u)
  have hm := sourceCutMultiplier_coeFn ψ hψ hb u
  rw [hu] at hm
  filter_upwards [SmallSupport.zeroExtend_coeFn hW (restrictL2 W u), hr, hm]
    with x hx hr hm
  rw [hx]
  by_cases hxW : x ∈ W
  · exact (indicator_of_mem hxW _).trans (hr hxW)
  · rw [indicator_of_notMem hxW]
    have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hxW (hs h))
    simpa only [hz, Complex.ofReal_zero, zero_smul] using hm.symm

/-- The local retarded output has EXACTLY the original whole-space zero
extension. Its producer is the literal mask identity, proved in `Support`.
Consumer: `retarded_local_negative_pairing_of_positive`. -/
theorem zeroExtend_localRetardedOperator_of_mask {U W : Set E}
    (hU : MeasurableSet U) (hW : MeasurableSet W) (Q : H →L[ℂ] H)
    (ψ : E → ℝ) (hψ : Continuous ψ) (hb : ∀ x, ‖ψ x‖ ≤ 1)
    (hs : tsupport ψ ⊆ W) (hQ : (sourceCutMultiplier ψ hψ hb).comp Q = Q)
    (f : LocalL2 U V) :
    SmallSupport.zeroExtend hW (localRetardedOperator hU W Q f) =
      Q (SmallSupport.zeroExtend hU f) := by
  apply zeroExtend_restrictL2_of_mask hW ψ hψ hb hs
  exact congrArg (fun A : H →L[ℂ] H ↦ A (SmallSupport.zeroExtend hU f)) hQ

end JanetCartan.RegularSector.Characteristic.RetardedLocalization
