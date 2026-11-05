module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.RealCompression

/-!
# Literal adjoints of physical plus-paired costs

Conjugation commutes with Hilbert adjunction of the whole factor. The real
compression likewise retains the actual real adjoint. Thus the costs apply
to the backward factors of `app:ch_regular:lem:finite-chain`, without
reordering masks or replacing the physical plus pairing.
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
local notation "H" => Lp F 2 (volume : Measure E)

/-- Literal conjugation and adjunction commute for the complete physical
factor, including both masks (`app:ch_regular:eq:chain-tail`). -/
theorem boundedConjugate_adjoint (T : H →L[ℂ] H) :
    (boundedConjugate T).adjoint = boundedConjugate T.adjoint := by
  let C : H ≃ₗᵢ[ℝ] H :=
    { (starL' ℝ : H ≃L[ℝ] H).toLinearEquiv with norm_map' := norm_star }
  have hC : (C : H →L[ℝ] H).adjoint = (C : H →L[ℝ] H) := by
    rw [C.adjoint_eq_symm]
    ext1 u
    change (starL' ℝ : H ≃L[ℝ] H).symm u = (starL' ℝ) u
    rw [symm_starL']
  have he (S : H →L[ℂ] H) : (boundedConjugate S).restrictScalars ℝ =
      (C : H →L[ℝ] H).comp ((S.restrictScalars ℝ).comp (C : H →L[ℝ] H)) := by
    ext1 u
    rfl
  have ha := congrArg (fun S : H →L[ℝ] H ↦ S.adjoint) (he T)
  simp only [adjoint_restrictScalars_complex, ContinuousLinearMap.adjoint_comp, hC,
    ContinuousLinearMap.comp_assoc] at ha
  have hb := ha.trans (he T.adjoint).symm
  ext1 u
  exact congrArg (fun S : H →L[ℝ] H ↦ S u) hb

/-- The adjoint of the physical finite plus pairing is the same plus pairing
of literal adjoints (`app:ch_regular:lem:finite-chain`). -/
theorem physicalPairedSectorSum_adjoint_eq {κ : Type*} (I : Finset κ)
    (T : κ → H →L[ℂ] H) :
    (physicalPairedSectorSum I T).adjoint =
      physicalPairedSectorSum I (fun j ↦ (T j).adjoint) := by
  simp [physicalPairedSectorSum, boundedConjugate_adjoint]

/-- Backward physical paired factors have the cost of their original literal
adjoints, on the same restriction scales (`app:ch_regular:eq:chain-tail`). -/
theorem physicalPairedSectorSum_adjoint_hasPolynomialRestrictionCost
    (ρ : ι → ℝ) (hρ : ∀ i, 1 ≤ ρ i) (T : κ → ι → H →L[ℂ] H) (I : Finset κ)
    (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hT : ∀ j ∈ I, HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale V F hV) ρ
      (fun i ↦ (localRetardedOperator hU V (T j i).adjoint).toLinearMap)) :
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale V F hV) ρ
      (fun i ↦ (localRetardedOperator hU V
        (physicalPairedSectorSum I (fun j ↦ T j i)).adjoint).toLinearMap) := by
  simp only [physicalPairedSectorSum_adjoint_eq]
  exact physicalPairedSectorSum_hasPolynomialRestrictionCost ρ hρ
    (fun j i ↦ (T j i).adjoint) I U V hU hV hT

private theorem adjoint_compressed_aux
    {X Y RX RY : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup RX] [InnerProductSpace ℝ RX] [CompleteSpace RX]
    [NormedAddCommGroup RY] [InnerProductSpace ℝ RY] [CompleteSpace RY]
    (A : X →L[ℝ] Y) (A' : Y →L[ℝ] X) (hA : A.adjoint = A')
    (P : Y →L[ℝ] RY) (J : RX →L[ℝ] X)
    (P' : RY →L[ℝ] Y) (J' : X →L[ℝ] RX)
    (hP : P.adjoint = P') (hJ : J.adjoint = J') :
    (P.comp (A.comp J)).adjoint = J'.comp (A'.comp P') := by
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    hP, hJ, hA, ContinuousLinearMap.comp_assoc]

/-- Local real compression retains the literal real Hilbert adjoint, with
the domains exchanged (`app:ch_regular:eq:chain-tail`). -/
theorem localRealCompression_adjoint {U V : Set E}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (T : H →L[ℂ] H) :
    (localRealCompression hU V T).adjoint = localRealCompression hV U T.adjoint := by
  have hJ : (l2ComplexInclusion (ι := Fin q) (volume.restrict U)).adjoint =
      l2RealPart (volume.restrict U) := by
    have he := congrArg ContinuousLinearMap.adjoint
      (l2RealPart_adjoint (ι := Fin q) (μ := volume.restrict U))
    simpa only [ContinuousLinearMap.adjoint_adjoint] using he.symm
  exact adjoint_compressed_aux (localRetardedOperator hU V T)
    (localRetardedOperator hV U T.adjoint) (localRetardedOperator_adjoint hU hV T)
    (l2RealPart (volume.restrict V)) (l2ComplexInclusion (volume.restrict U))
    (l2ComplexInclusion (volume.restrict V)) (l2RealPart (volume.restrict U))
    (l2RealPart_adjoint (volume.restrict V)) hJ

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
