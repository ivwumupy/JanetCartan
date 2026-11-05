module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.SourceGerms
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.PhysicalInverse

/-!
# Normalized germs of the entire selected physical algebraic symbol

The original doubled multiplier stays inside the symbol. The coefficient
first-jet formula exposes the order-minus-one factor before taking any joint
derivative. All source derivatives and the full `B` are retained through
the proved source-plateau germ (`energy-complete-residual`, `high-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo RegularSector.FiniteAssembly
open CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

private theorem physical_action_frequency_smul
    (A : E → Fin (d+1) → CMat) (B : E → CMat) (b : E → E → CMat)
    (β : E → ℂ) (y ξ : E) (hb : DifferentiableAt ℝ (fun y ↦ b y ξ) y) :
    physicalSymbolApply A B (fun y ξ ↦ β ξ • b y ξ) y ξ =
      β ξ • physicalSymbolApply A B b y ξ := by
  have hd : fderiv ℝ (fun z ↦ β ξ • b z ξ) y =
      β ξ • fderiv ℝ (fun z ↦ b z ξ) y := fderiv_const_smul hb (β ξ)
  simp only [physicalSymbolApply, partialDeriv, hd, _root_.smul_apply,
    Matrix.mul_smul, smul_add, Finset.smul_sum]

/-- The selected physical action at a normalized frequency is exactly the
original multiplier times the first-jet coefficient action, with its factor
`ρ⁻¹` displayed. This is an identity of the ENTIRE direct algebraic symbol
on the source plateau (`energy-complete-residual`). -/
theorem selected_algebraic_normalized_eq_coefficient_action
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {threshold ρ : ℝ} (ht : f.radialThreshold ≤ threshold) (hρ : 0 < ρ)
    (Q : E → Coeff) (B : E → Mat) (y ξ : E)
    (hy : physicalCoordinates (f.chart p).index y ∈ ball x (4*f.physicalRadius))
    (hQ : DifferentiableAt ℝ Q (physicalCoordinates (f.chart p).index y))
    (hG : DifferentiableAt ℝ (coefficientConicBminus (f.chart p).radialSection
      (f.chart p).index (f.chart p).row (f.chart p).col (f.chart p).root)
      (Q (physicalCoordinates (f.chart p).index y), ξ)) :
    selectedAlgebraicSymbol f p (2*threshold) Q B 1 y (ρ • ξ) =
      ρ⁻¹ • (selectedEndpointMultiplier f p threshold (ρ • ξ) •
        coefficientConicPhysicalAction (f.chart p).radialSection (f.chart p).index
          (f.chart p).row (f.chart p).col (f.chart p).root
          ((Q (physicalCoordinates (f.chart p).index y),
            (fderiv ℝ Q (physicalCoordinates (f.chart p).index y),
              B (physicalCoordinates (f.chart p).index y))), ξ)) := by
  let c := f.chart p
  let b := conicBminus c.radialSection c.index Q
    (fieldRoot (coordinateSplit c.index) Q c.root) c.row c.col
  have hb : DifferentiableAt ℝ (fun z ↦ b z ξ) y := by
    change DifferentiableAt ℝ (coefficientConicBminus c.radialSection c.index c.row c.col c.root ∘
      (fun z ↦ (Q (physicalCoordinates c.index z), ξ))) y
    have hin : DifferentiableAt ℝ (fun z : E ↦ (Q (physicalCoordinates c.index z), ξ)) y :=
      (hQ.comp y (physicalCoordinates c.index).differentiableAt).prodMk (differentiableAt_const ξ)
    exact hG.comp y hin
  have he : (fun z ↦ b z (ρ • ξ)) = fun z ↦ ρ⁻¹ • b z ξ := by
    funext z
    exact coefficientConicBminus_smul c.radialSection c.index c.row c.col c.root hρ.ne' _ ξ
  have hbr : DifferentiableAt ℝ (fun z ↦ b z (ρ • ξ)) y := by
    rw [he]
    exact hb.const_smul ρ⁻¹
  rw [selected_algebraic_physical_action_on_common_ball f p ht Q B hy,
    physical_action_frequency_smul _ _ b _ y (ρ • ξ) hbr,
    physicalSymbolApply_conicBminus_rescale c.radialSection c.index c.row c.col c.root Q B hρ y ξ hb,
    physicalSymbolApply_conicBminus_eq_coefficient_action c.radialSection c.index c.row c.col c.root Q B y ξ hQ hG]
  exact smul_comm _ _ _

/-- Joint germ version of the normalized identity. Smoothness is required
only at the actual coefficient/full-covector point and is supplied by the
retained inverse construction; no derivative estimate is assumed. Every
normalized covariable derivative therefore retains the literal `ρ⁻¹`
factor (`app:ch_regular:eq:high-amplitude`). -/
theorem selected_algebraic_normalized_eventuallyEq_coefficient_action
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {threshold ρ : ℝ} (ht : f.radialThreshold ≤ threshold) (hρ : 0 < ρ)
    (Q : E → Coeff) (B : E → Mat) (v : E × E)
    (hv : physicalCoordinates (f.chart p).index v.1 ∈ ball x (4*f.physicalRadius))
    (hQ : ContDiffAt ℝ ∞ Q (physicalCoordinates (f.chart p).index v.1))
    (hG : ContDiffAt ℝ ∞ (coefficientConicBminus (f.chart p).radialSection
      (f.chart p).index (f.chart p).row (f.chart p).col (f.chart p).root)
      (Q (physicalCoordinates (f.chart p).index v.1), v.2)) :
    (fun w : E × E ↦ selectedAlgebraicSymbol f p (2*threshold) Q B 1 w.1 (ρ • w.2)) =ᶠ[𝓝 v]
      fun w : E × E ↦ ρ⁻¹ • (selectedEndpointMultiplier f p threshold (ρ • w.2) •
        coefficientConicPhysicalAction (f.chart p).radialSection (f.chart p).index
          (f.chart p).row (f.chart p).col (f.chart p).root
          ((Q (physicalCoordinates (f.chart p).index w.1),
            (fderiv ℝ Q (physicalCoordinates (f.chart p).index w.1),
              B (physicalCoordinates (f.chart p).index w.1))), w.2)) := by
  have hπ : Continuous (fun w : E × E ↦ physicalCoordinates (f.chart p).index w.1) :=
    (physicalCoordinates (f.chart p).index).continuous.comp continuous_fst
  have hF : ContinuousAt (fun w : E × E ↦ (Q (physicalCoordinates (f.chart p).index w.1), w.2)) v :=
    (hQ.continuousAt.comp (f := fun w : E × E ↦ physicalCoordinates (f.chart p).index w.1)
      hπ.continuousAt).prodMk continuousAt_snd
  filter_upwards [hπ.continuousAt.eventually (isOpen_ball.mem_nhds hv),
    hπ.continuousAt.eventually ((hQ.of_le (m := (1 : ℕ∞ω)) (by simp)).eventually (by simp)),
    hF.eventually ((hG.of_le (m := (1 : ℕ∞ω)) (by simp)).eventually (by simp))] with w hw hqw hgw
  exact selected_algebraic_normalized_eq_coefficient_action f p ht hρ Q B w.1 w.2 hw
    hqw.differentiableAt_one hgw.differentiableAt_one

/-- The complete physical algebraic symbol vanishes at every zero of its
original frequency multiplier, including all differentiated source terms.
This provides zero germs outside the actual closed frequency support
(`app:ch_regular:eq:high-amplitude`). -/
theorem selected_algebraic_symbol_zero_of_multiplier_zero
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (threshold : ℝ)
    (Q : E → Coeff) (B : E → Mat) (y ξ : E)
    (hβ : selectedEndpointMultiplier f p threshold ξ = 0) :
    selectedAlgebraicSymbol f p (2*threshold) Q B 1 y ξ = 0 := by
  let c := f.chart p
  let b := directAlgebraicSymbol
    (conicBminus c.radialSection c.index Q (fieldRoot (coordinateSplit c.index) Q c.root) c.row c.col)
    (conicSourceSymbol c.radialSection (conicMask (f.spatialMask p)) c.sourceMask)
    (selectedEndpointMultiplier f p threshold)
  have he : (fun z ↦ b z ξ) = fun _ ↦ (0 : CMat) := by
    funext z
    simp only [b, directAlgebraicSymbol, hβ, mul_zero, zero_smul]
  change physicalSymbolApply
    (fun y a ↦ (coefficient c.index Q y a).map Complex.ofReal)
    (fun y ↦ (zeroth c.index B y).map Complex.ofReal) b y ξ = 0
  simp only [physicalSymbolApply, partialDeriv, he, fderiv_const_apply, _root_.zero_apply,
    mul_zero, Finset.sum_const_zero, zero_add]
  rw [congrFun he y, mul_zero]

/-- Local joint smoothness of the normalized complete symbol on the output
plateau, directly from the retained coefficient inverse. This is used to
restrict the comparable grade to physical slices for the noncomparable
estimate (`app:ch_regular:eq:high-amplitude`, `chain-tail`). -/
theorem contDiffAt_selected_algebraic_normalized_on_output
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {threshold ρ : ℝ} (ht : f.radialThreshold ≤ threshold) (hρ : 0 < ρ)
    (Q : E → Coeff) (B : E → Mat) (v : E × E)
    (hv : physicalCoordinates (f.chart p).index v.1 ∈ ball x (4*f.physicalRadius))
    (hQ : ContDiffAt ℝ ∞ Q (physicalCoordinates (f.chart p).index v.1))
    (hB : ContDiffAt ℝ ∞ B (physicalCoordinates (f.chart p).index v.1))
    (hG : ContDiffAt ℝ ∞ (coefficientConicBminus (f.chart p).radialSection
      (f.chart p).index (f.chart p).row (f.chart p).col (f.chart p).root)
      (Q (physicalCoordinates (f.chart p).index v.1), v.2)) :
    ContDiffAt ℝ ∞ (fun w : E × E ↦
      selectedAlgebraicSymbol f p (2*threshold) Q B 1 w.1 (ρ • w.2)) v := by
  have hP : ContDiff ℝ ∞ (fun w : E × E ↦ physicalCoordinates (f.chart p).index w.1) :=
    (physicalCoordinates (f.chart p).index).contDiff.comp contDiff_fst
  have hparam := ((hQ.comp v hP.contDiffAt).prodMk
    (((hQ.fderiv_right (m := ∞) (by simp)).comp v hP.contDiffAt).prodMk
      (hB.comp v hP.contDiffAt))).prodMk contDiffAt_snd
  have hcf := (contDiffAt_coefficientConicPhysicalAction _ _ _ _ _ _ hG).comp v hparam
  have hβ : ContDiffAt ℝ ∞ (fun w : E × E ↦ selectedEndpointMultiplier f p threshold (ρ • w.2)) v :=
    ((selectedEndpointMultiplier_bounds f p threshold).1.comp (contDiff_snd.const_smul ρ)).contDiffAt
  exact ((hβ.smul hcf).const_smul ρ⁻¹).congr_of_eventuallyEq
    (selected_algebraic_normalized_eventuallyEq_coefficient_action f p ht hρ Q B v hv hQ hG)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
