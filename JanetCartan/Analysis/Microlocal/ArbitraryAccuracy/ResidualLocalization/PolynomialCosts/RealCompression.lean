module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Pairing

/-!
# Real compression of the physical complete factors

The existing real inclusion and real part act on the same local L² spaces.
Their composition is identified a.e. with restriction of the literal global
real compression applied to the original zero extension. No anti-real pairing
or additional normalization enters `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped JanetCartan.RegularSector.Realization
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
open LocalSobolev ResponseTransfer RegularSector.Realization
open RegularSector.Characteristic.RetardedLocalization
open CharacteristicTransport.CompleteResidual
variable {d q : ℕ} {ι κ : Type*}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "RF" => EuclideanSpace ℝ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

/-- Real compression on the existing restriction spaces, using exactly the
same whole-space operator and original zero extension. Its literal a.e.
identification is `localRealCompression_coeFn`
(`app:ch_regular:lem:finite-chain`). -/
def localRealCompression {U : Set E} (hU : MeasurableSet U) (V : Set E)
    (T : H →L[ℂ] H) : LocalL2 U RF →L[ℝ] LocalL2 V RF :=
  (l2RealPart (volume.restrict V)).comp
    ((localRetardedOperator hU V T).comp (l2ComplexInclusion (volume.restrict U)))

/-- This is the literal restriction of global real compression, on the
literal zero-extended input (`app:ch_regular:eq:chain-tail`). -/
theorem localRealCompression_coeFn {U : Set E} (hU : MeasurableSet U) (V : Set E)
    (T : H →L[ℂ] H) (u : LocalL2 U RF) :
    localRealCompression hU V T u =ᵐ[volume.restrict V]
      realCompression T (SmallSupport.zeroExtend hU u) := by
  have he := compLp_zeroExtend (euclideanComplexInclusion (ι := Fin q)) hU u
  change l2ComplexInclusion volume (SmallSupport.zeroExtend hU u) =
    SmallSupport.zeroExtend hU (l2ComplexInclusion (volume.restrict U) u) at he
  change l2RealPart (volume.restrict V)
    (restrictL2 V (T (SmallSupport.zeroExtend hU (l2ComplexInclusion (volume.restrict U) u))))
      =ᵐ[volume.restrict V] l2RealPart volume
        (T (l2ComplexInclusion volume (SmallSupport.zeroExtend hU u)))
  rw [← he]
  filter_upwards [euclideanRealPart.coeFn_compLpL
      (restrictL2 V (T (l2ComplexInclusion volume (SmallSupport.zeroExtend hU u)))),
    restrictL2_coeFn V (T (l2ComplexInclusion volume (SmallSupport.zeroExtend hU u))),
    ae_restrict_of_ae (euclideanRealPart.coeFn_compLpL
      (T (l2ComplexInclusion volume (SmallSupport.zeroExtend hU u))))] with x hx hy hz
  exact hx.trans ((congrArg euclideanRealPart hy).trans hz.symm)

/-- The literal real compression inherits the actual complex factor's proved
restriction cost, via the genuine weak-extension estimates for inclusion and
real part (`app:ch_regular:eq:chain-tail`). -/
theorem realCompression_hasPolynomialRestrictionCost
    (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (T : ι → H →L[ℂ] H)
    (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hT : HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale V F hV) ρ
      (fun i ↦ (localRetardedOperator hU V (T i)).toLinearMap)) :
    HasPolynomialSobolevCost (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale V RF hV) ρ
      (fun i ↦ (localRealCompression hU V (T i)).toLinearMap) := by
  exact polynomialCost_comp (restrictionSobolevScale U RF hU)
    (restrictionSobolevScale V F hV) (restrictionSobolevScale V RF hV) hρ
    (compLp_hasPolynomialRestrictionCost ρ (euclideanRealPart (ι := Fin q)) V hV)
    (polynomialCost_comp (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale U F hU) (restrictionSobolevScale V F hV) hρ hT
      (compLp_hasPolynomialRestrictionCost ρ (euclideanComplexInclusion (ι := Fin q)) U hU))

/-- The finite physical plus pairing and its literal real compression have
polynomial cost on the genuine real restriction scale. The complex sector
costs are supplied by the concrete direct-factor assembly, with all masks
and lower-order terms retained (`app:ch_regular:eq:chain-tail`). -/
theorem realPhysicalPairedSectorSum_hasPolynomialRestrictionCost
    (ρ : ι → ℝ) (hρ : ∀ i, 1 ≤ ρ i) (T : κ → ι → H →L[ℂ] H) (I : Finset κ)
    (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hT : ∀ j ∈ I, HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale V F hV) ρ
      (fun i ↦ (localRetardedOperator hU V (T j i)).toLinearMap)) :
    HasPolynomialSobolevCost (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale V RF hV) ρ
      (fun i ↦ (localRealCompression hU V
        (physicalPairedSectorSum I (fun j ↦ T j i))).toLinearMap) :=
  realCompression_hasPolynomialRestrictionCost ρ (fun i ↦ zero_lt_one.trans_le (hρ i))
    _ U V hU hV (physicalPairedSectorSum_hasPolynomialRestrictionCost ρ hρ T I U V hU hV hT)

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
