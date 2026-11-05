module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.PdoIdentification
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.DirectOperators

/-!
# The finite solver as the sum of the same common-chart operators

Identify the actual finite operators with the local operators used in the
common-chart differential equation. Source and output multiplication remain
on their original sides. The identical enlarged `2*L` multiplier occurs in
all four PDO symbols. Consumer: finite summation of
`SelectedChart.completeResidual_of_common_selected_chart`, for
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
open Characteristic Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open Characteristic.PdoRealization FiniteAssembly FiniteEvolution FiniteAlgebraic FinitePdo
open FiniteMasks FiniteMasks.ActualFamily FourierIntegral LowBounds
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- The retained chart evolution with the final common physical masks. This
is the `Mo ∘ retained ∘ Mi` in the tested common-chart equation, with source
multiplication still before Fourier multiplication (`energy-complete-residual`). -/
def selectedCommonChartRetarded
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  let e := physicalCoordinates (f.chart p).index
  (sourceCutMultiplier (output ∘ e) (ho.comp e.continuous) (fun y ↦ hob (e y))).comp
    (T.comp (sourceCutMultiplier (f.inputMask ∘ e)
      (f.inputMask_smooth.continuous.comp e.continuous) (fun y ↦ hib (e y))))

/-- Both physical masks commute with the coordinate pullback in their literal
order. This identifies the retained chart factors without commuting the input
mask past the evolution or its Fourier multiplier (`energy-complete-residual`). -/
theorem physicalOperator_selectedCommonChartRetarded
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : H →L[ℂ] H) :
    physicalOperator (f.chart p).index (selectedCommonChartRetarded f p output ho hob hib T) =
      (sourceCutMultiplier output ho hob).comp
        ((physicalOperator (f.chart p).index T).comp
          (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib)) := by
  ext1 u
  apply (physicalPullbackL2 (f.chart p).index).injective
  simp only [selectedCommonChartRetarded, physicalOperator_apply,
    ContinuousLinearMap.comp_apply, LinearIsometryEquiv.apply_symm_apply,
    physicalPullbackL2_sourceCutMultiplier]

/-- The final masked evolution sum equals the sum of the exact common-chart
factors used in the PDE identity (`energy-complete-residual`). -/
theorem finitePhysicalOperator_selectedCommonChartRetarded
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : f.centers → H →L[ℂ] H) :
    finitePhysicalOperator (fun p ↦ (f.chart p).index)
      (fun p ↦ selectedCommonChartRetarded f p output ho hob hib (T p)) =
      (sourceCutMultiplier output ho hob).comp
        ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
          (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib)) := by
  classical
  ext1 u
  simp only [finitePhysicalOperator, physicalOperator_selectedCommonChartRetarded,
    ContinuousLinearMap.comp_apply, sum_apply, map_sum]

/-- The local two-term solver in the common-chart equation, expressed with the
literal selected inverse symbol at `2*L` (`energy-complete-residual`). -/
def selectedCommonChartSolver
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  selectedCommonChartRetarded f p output ho hob hib T + (1 / Complex.I) •
    maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
      (selectedAlgebraicSymbol f p (2*L) Q B 0)

/-- All three local residual terms, with the upper endpoint and full `B`
contribution. The angular identity defect is separate (`energy-complete-residual`). -/
def selectedCommonChartResidual
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat) (W₁ : TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
      (selectedEndpointSymbol f p L Q W₁) +
    selectedCommonChartRetarded f p output ho hob hib T + (1 / Complex.I) •
      maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B 1)

private theorem finitePhysicalOperator_add {ι : Type*} [Fintype ι]
    (i : ι → Fin (d+1)) (S T : ι → H →L[ℂ] H) :
    finitePhysicalOperator i (fun p ↦ S p + T p) =
      finitePhysicalOperator i S + finitePhysicalOperator i T := by
  ext1 u
  simp [finitePhysicalOperator, physicalOperator_apply, Finset.sum_add_distrib]

private theorem finitePhysicalOperator_smul {ι : Type*} [Fintype ι]
    (i : ι → Fin (d+1)) (a : ℂ) (T : ι → H →L[ℂ] H) :
    finitePhysicalOperator i (fun p ↦ a • T p) = a • finitePhysicalOperator i T := by
  ext1 u
  simp [finitePhysicalOperator, physicalOperator_apply, Finset.smul_sum]

/-- Identify the SAME finite solver with its common-chart sum, using the
proved algebraic realization on each selected chart. These normal budgets
are the local outputs of `exists_finite_algebraic_pdo_sums`; no operator
identity or differential equation is assumed (`energy-complete-residual`). -/
theorem selectedFiniteDirectSolver_eq_commonChartSum
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (R C : f.centers → ℝ)
    (hb : ∀ p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B 0)) (R p) (C p))
    (T : f.centers → H →L[ℂ] H) :
    selectedFiniteDirectSolver f L Q B output ho hob
      ((sourceCutMultiplier output ho hob).comp
        ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
          (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))) =
      finitePhysicalOperator (fun p ↦ (f.chart p).index)
        (fun p ↦ selectedCommonChartSolver f p L Q B output ho hob hib (T p)) := by
  rw [selectedFiniteDirectSolver,
    selectedFiniteAlgebraicPDO_commonOutput f L Q B 0 output ho hob hsupp R C hb]
  simp only [selectedCommonChartSolver, finitePhysicalOperator_add,
    finitePhysicalOperator_smul, finitePhysicalOperator_selectedCommonChartRetarded,
    one_div, Complex.inv_I]

/-- Identify all THREE residual summands on the SAME final common masks and
threshold. The retarded upper endpoint is not dropped (`energy-complete-residual`). -/
theorem selectedFiniteDirectResidual_eq_commonChartSum
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (R C : f.centers → ℝ)
    (hb : ∀ p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B 1)) (R p) (C p))
    (T : f.centers → H →L[ℂ] H) :
    selectedFiniteDirectResidual f L Q B W₁ output ho hob
      ((sourceCutMultiplier output ho hob).comp
        ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
          (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))) =
      finitePhysicalOperator (fun p ↦ (f.chart p).index)
        (fun p ↦ selectedCommonChartResidual f p L Q B (W₁ p) output ho hob hib (T p)) := by
  rw [selectedFiniteDirectResidual,
    selectedFiniteAlgebraicPDO_commonOutput f L Q B 1 output ho hob hsupp R C hb]
  simp only [selectedCommonChartResidual, finitePhysicalOperator_add,
    finitePhysicalOperator_smul, finitePhysicalOperator_selectedCommonChartRetarded,
    selectedFiniteEndpointPDO, one_div, Complex.inv_I]

/-- The source-plus-residual sum is I plus the complete error with ONE final
identity subtraction. The source PDO is the identical enlarged-threshold
operator used by the terminal angular localization (`prop:complete-residual`). -/
theorem selectedFiniteCompleteError_eq_commonChartSum
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (R C : f.centers → ℝ)
    (hb : ∀ p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B 1)) (R p) (C p))
    (T : f.centers → H →L[ℂ] H) :
    1 + selectedFiniteCompleteError f L Q B W₁ output ho hob
      ((sourceCutMultiplier output ho hob).comp
        ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
          (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))) =
      finitePhysicalOperator (fun p ↦ (f.chart p).index)
        (fun p ↦ maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
          (selectedSourceSymbol f p (2*L)) +
          selectedCommonChartResidual f p L Q B (W₁ p) output ho hob hib (T p)) := by
  rw [← selectedFiniteCompleteError_identity,
    selectedFiniteDirectResidual_eq_commonChartSum f L Q B W₁ output ho hob hib hsupp R C hb T,
    finitePhysicalOperator_add, selectedFiniteSourcePDO_commonOutput f L hL output ho hob hsupp]

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
