module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.Carriers
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.PhysicalBudget

/-!
# Physical action of the coefficient-level conic inverse

The first jet of the original coefficient field determines the complete
physical action, including `B`. Its coefficient/full-covector smoothness is
proved before restricting to physical slices. This is consumed by the joint
grade for branch three of `CompleteFactor` (`energy-complete-residual`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.AlgebraicSymbols
open CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "Coeff" => Fin (d + 1) → Mat
local notation "Jet" => Coeff × ((E →L[ℝ] Coeff) × Mat)

/-- The physical action of the same coefficient inverse, as a function of
the original first coefficient jet, full `B`, and full covector. The first
derivative acts only in coefficient directions (`energy-complete-residual`). -/
def coefficientConicPhysicalAction (ℓ : Euclidean d →L[ℝ] ℝ) (i r c : Fin (d+1))
    (H : Coeff × Euclidean d → ℝ) (v : Jet × E) : CMat :=
  let G := coefficientConicBminus ℓ i r c H
  (∑ a, (pencil v.1.1 (physicalCoordinates i (EuclideanSpace.single a 1))).map Complex.ofReal *
    fderiv ℝ G (v.1.1, v.2) (v.1.2.1 (physicalCoordinates i (EuclideanSpace.single a 1)), 0)) +
      v.1.2.2.map Complex.ofReal * G (v.1.1, v.2)

/-- Smoothness of the complete physical coefficient action follows from
the retained inverse germ. In applications that germ is constructed from
`RootBuffer` and the original complement certificate (`high-amplitude`). -/
theorem contDiffAt_coefficientConicPhysicalAction
    (ℓ : Euclidean d →L[ℝ] ℝ) (i r c : Fin (d+1)) (H : Coeff × Euclidean d → ℝ)
    (v : Jet × E) (hG : ContDiffAt ℝ ∞ (coefficientConicBminus ℓ i r c H) (v.1.1, v.2)) :
    ContDiffAt ℝ ∞ (coefficientConicPhysicalAction ℓ i r c H) v := by
  have hπ : ContDiffAt ℝ ∞ (fun v : Jet × E ↦ (v.1.1, v.2)) v :=
    contDiffAt_fst.fst.prodMk contDiffAt_snd
  have hg := hG.comp v hπ
  have hd := (hG.fderiv_right (m := ∞) (by simp)).comp v hπ
  apply ContDiffAt.add
  · apply ContDiffAt.sum
    intro a _
    exact (contDiff_matrix_map_ofReal.contDiffAt.comp v
      (contDiff_pencil.contDiffAt.comp v (contDiffAt_fst.fst.prodMk contDiffAt_const))).mul
      (hd.clm_apply ((contDiffAt_fst.snd.fst.clm_apply contDiffAt_const).prodMk contDiffAt_const))
  · exact (contDiff_matrix_map_ofReal.contDiffAt.comp v contDiffAt_fst.snd.snd).mul hg

/-- Substitution of the ORIGINAL coefficient first jet gives the literal
physical inverse action. There is no differentiated-kernel input and no
replacement inverse (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem physicalSymbolApply_conicBminus_eq_coefficient_action
    (ℓ : Euclidean d →L[ℝ] ℝ) (i r c : Fin (d+1)) (H : Coeff × Euclidean d → ℝ)
    (Q : E → Coeff) (B : E → Mat) (y ξ : E)
    (hQ : DifferentiableAt ℝ Q (physicalCoordinates i y))
    (hG : DifferentiableAt ℝ (coefficientConicBminus ℓ i r c H)
      (Q (physicalCoordinates i y), ξ)) :
    physicalSymbolApply (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
      (fun y ↦ (zeroth i B y).map Complex.ofReal)
      (conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c) y ξ =
    coefficientConicPhysicalAction ℓ i r c H
      ((Q (physicalCoordinates i y), (fderiv ℝ Q (physicalCoordinates i y), B (physicalCoordinates i y))), ξ) := by
  have hin : HasFDerivAt (fun z : E ↦ (Q (physicalCoordinates i z), ξ))
      ((fderiv ℝ Q (physicalCoordinates i y)).comp (physicalCoordinates i).toContinuousLinearMap |>.prod 0) y :=
    (hQ.hasFDerivAt.comp y (physicalCoordinates i).hasFDerivAt).prodMk (hasFDerivAt_const ξ y)
  have hd := hG.hasFDerivAt.comp y hin
  have he : (fun z ↦ conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c z ξ) =
      coefficientConicBminus ℓ i r c H ∘ (fun z ↦ (Q (physicalCoordinates i z), ξ)) := rfl
  simp only [physicalSymbolApply, partialDeriv, he, hd.fderiv, coefficientConicPhysicalAction,
    coefficient, zeroth, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearEquiv.coe_coe, _root_.zero_apply]
  rfl

/-- Positive frequency scaling factors out BEFORE physical differentiation,
so the complete inverse action retains order minus one, including `B`.
Consumer: the normalized joint algebraic profile (`high-amplitude`). -/
theorem physicalSymbolApply_conicBminus_rescale
    (ℓ : Euclidean d →L[ℝ] ℝ) (i r c : Fin (d+1)) (H : Coeff × Euclidean d → ℝ)
    (Q : E → Coeff) (B : E → Mat) {ρ : ℝ} (hρ : 0 < ρ) (y ξ : E)
    (hb : DifferentiableAt ℝ
      (fun y ↦ conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c y ξ) y) :
    physicalSymbolApply (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
      (fun y ↦ (zeroth i B y).map Complex.ofReal)
      (conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c) y (ρ • ξ) =
    ρ⁻¹ • physicalSymbolApply (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
      (fun y ↦ (zeroth i B y).map Complex.ofReal)
      (conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c) y ξ := by
  have he : (fun z ↦ conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c z (ρ • ξ)) =
      fun z ↦ ρ⁻¹ • conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c z ξ := by
    funext z
    exact coefficientConicBminus_smul ℓ i r c H hρ.ne' _ ξ
  have hv := congrFun he y
  have hd : fderiv ℝ (fun z ↦ ρ⁻¹ • conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c z ξ) y =
      ρ⁻¹ • fderiv ℝ (fun z ↦ conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c z ξ) y := by
    exact fderiv_const_smul hb ρ⁻¹
  simp only [physicalSymbolApply, partialDeriv, he,
    hd, _root_.smul_apply,
    hv, Matrix.mul_smul, Finset.smul_sum, smul_add]

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
