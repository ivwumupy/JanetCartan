module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Localization
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Regularizations.Identification

/-!
# The complete operators with the literal common masks

Identify the complete solver and all three residual terms with localization
of the original canonical family. The source multiplier is applied before
the Fourier multiplier. Consumer: the common measurement equation before
finite summation (`app:ch_regular_base:eq:energy-complete-residual`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.SelectedChart
open Characteristic Characteristic.ResidualCoordinates Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral Characteristic.PdoRealization
open Characteristic.EvolutionIntegral.UncutTestAction
open FourierIntegral FourierIntegral.LowBounds Pseudodifferential
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "H" => SpacetimeL2 d (d+1)
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- The SAME retained solver and full physical residual, with the exact
common input and output masks from `PhysicalConstruction`, are localization
of the canonical complete solver and residual. The literal retarded test
actions are constructed by `exists_selected_supported_graph_regularizations`;
the PDO normal budgets are those of the three named PDO producers.
This is an operator identification, not an assumed differential equation.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem selected_common_complete_operators
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat) (Δ a : ℝ)
    (Ψ : TwoTimePhase d) (W₀ W₁ : TwoTimeAmplitude d (d+1))
    (bm : E → E → CMat) (σ : E → Euclidean d → ℂ) (β : E → ℂ)
    (χout χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hout : tsupport output ⊆ ball x f.physicalRadius)
    (hlocalout : ∀ y, (output y : ℂ) * χout ((physicalCoordinates (f.chart p).index).symm y) = (output y : ℂ))
    (hlocalin : ∀ y, χsource ((physicalCoordinates (f.chart p).index).symm y) *
      (f.inputMask y : ℂ) = (f.inputMask y : ℂ)) :
    let e := physicalCoordinates (f.chart p).index
    let A : E → Fin (d+1) → CMat := fun y i ↦ (coefficient (f.chart p).index Q y i).map Complex.ofReal
    let Bc : E → CMat := fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal
    let b : Bool → TwoTimeAmplitude d (d+1) := directRetardedAmplitudes A Bc W₀ W₁
    let sym : Fin 4 → E → E → CMat := directPDOSymbols A Bc W₁ bm σ β
    ∀ (canonical retained : Bool → H →L[ℂ] H) (C : Bool → ℝ) (Cs : Bool → ℕ → ℝ),
    (∀ k u, canonical k (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (retardedPhysicalIntegral Ψ (b k) (chartOutputMask f p) (chartInputMask f p) β
        (chartPhysicalMasks_properties f p).2.1 a u y)) →
    (∀ k, RetainedSignedRetardedBounds (closedBall x RQ) Q B Δ a Ψ (b k)
      χout χsource β hs (if k then 1 else 0) (C k) (Cs k) (retained k)) →
    ∀ (Rbox Mbound : Fin 4 → ℝ),
    (∀ k, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p) (sym k))
      (Rbox k) (Mbound k)) →
    let Mo : H →L[ℂ] H := sourceCutMultiplier (r := d+1) (fun y ↦ output (e y))
      (ho.comp e.continuous) (fun y ↦ hob (e y))
    let Mi : H →L[ℂ] H := sourceCutMultiplier (r := d+1) (fun y ↦ f.inputMask (e y))
      (f.inputMask_smooth.continuous.comp e.continuous) (fun y ↦ by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (f.inputMask_range (e y)).1]
          using (f.inputMask_range (e y)).2)
    let P : Fin 4 → H →L[ℂ] H := fun k ↦ maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p) (sym k)
    let Pc : Fin 4 → H →L[ℂ] H := fun k ↦ maskedPhysicalPDO (fun y ↦ (output (e y) : ℂ)) (chartInputMask f p) (sym k)
    let S : H →L[ℂ] H := Mo.comp ((retained false).comp Mi) + (1 / Complex.I) • Pc 0
    let R : H →L[ℂ] H := Pc 2 + Mo.comp ((retained true).comp Mi) + (1 / Complex.I) • Pc 3
    S = Mo.comp (canonical false + (1 / Complex.I) • P 0) ∧
      R = Mo.comp (P 2 + canonical true + (1 / Complex.I) • P 3) ∧
      Pc 1 + R = Mo.comp (P 1 + (P 2 + canonical true + (1 / Complex.I) • P 3)) ∧
      Pc 1 + R = ContinuousLinearMap.id ℂ H + ((Pc 1 - ContinuousLinearMap.id ℂ H) + R) := by
  intro e A Bc b sym canonical retained C Cs hcanonical hret Rbox Mbound hbudget Mo Mi P Pc S R
  have hj (k : Bool) : Mo.comp (canonical k) = Mo.comp ((retained k).comp Mi) :=
    retained_common_localization_eq_canonical f p Q B Δ a Ψ (b k) β (canonical k)
      (hcanonical k) χout χsource hs (if k then 1 else 0) (C k) (Cs k) (retained k)
      (hret k) output ho hob hout hlocalout hlocalin
  have hp (k : Fin 4) : Mo.comp (P k) = Pc k :=
    sourceCutMultiplier_maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p)
      (sym k) (Rbox k) (Mbound k) (hbudget k) (fun y ↦ output (e y))
      (ho.comp e.continuous) (fun y ↦ hob (e y)) (commonOutput_mul_chartOutputMask f p output hout)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, hj, hp, S]
  · simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, hj, hp, R]
  · simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, hj, hp, R]
  · abel

end JanetCartan.RegularSector.FiniteResidual.SelectedChart
