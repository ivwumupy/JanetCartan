module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.Operators
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.TestedSum

/-!
# Finite physical assembly of the direct tested equation

This consumes the same common-chart equations and actual algebraic normal
budgets returned by the selected construction. The original physical solver,
all three residual terms and the full source-minus-identity defect are the
operators of `FiniteAssembly.DirectOperators`. No differential equation for
the finite sum is assumed. Instantiating the per-chart equations on the
retained phase/amplitude witnesses remains the sector constructor's task.

Sources: `app:ch_regular_base:eq:sector-theorem-identity`,
`app:ch_regular_base:prop:complete-residual`, and
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
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

/-- The tested equation for the literal finite solver has the entire source
PDO plus all THREE residual terms. The only equation premise is the local
output of `completeResidual_of_common_selected_chart` on the SAME operators.
Normal budgets are the actual algebraic construction's outputs. The complete
error retains one final identity subtraction (`energy-complete-residual`). -/
theorem selectedFiniteDirectSolver_test_of_commonCharts
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L)
    (hΩ : IsOpen Ω) {U : Set E} (hUΩ : U ⊆ Ω)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (R C : Fin 2 → f.centers → ℝ)
    (hb : ∀ o p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B o)) (R o p) (C o p))
    (Op : Fin 2 → f.centers → H →L[ℂ] H)
    (ht : ∀ p u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ physicalCoordinates (f.chart p).index ⁻¹' U → ∀ j,
      physicalTestAction (coefficient (f.chart p).index Q) (zeroth (f.chart p).index B)
        (fun y ↦ (selectedCommonChartSolver f p L Q B output ho hob hib (Op 0 p) u y).ofLp)
        φ j = ∫ y, φ y •
          ((maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
            (selectedSourceSymbol f p (2*L)) +
            selectedCommonChartResidual f p L Q B (W₁ p) output ho hob hib (Op 1 p)) u) y j) :
    let retarded := fun o : Fin 2 ↦ (sourceCutMultiplier output ho hob).comp
      ((finitePhysicalOperator (fun p ↦ (f.chart p).index) (Op o)).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
    let S := selectedFiniteDirectSolver f L Q B output ho hob (retarded 0)
    let Efull := selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1)
    ∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ j,
      physicalTestAction
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (S u y).ofLp) φ j = ∫ y, φ y • ((1 + Efull) u) y j := by
  intro retarded S Efull u φ hφ hc hs j
  have hS := selectedFiniteDirectSolver_eq_commonChartSum f L Q B output ho hob hib hsupp
    (R 0) (C 0) (hb 0) (Op 0)
  have hT := selectedFiniteCompleteError_eq_commonChartSum f L hL Q B W₁ output ho hob hib hsupp
    (R 1) (C 1) (hb 1) (Op 1)
  change S = _ at hS
  change 1 + Efull = _ at hT
  rw [hS, hT]
  exact finitePhysicalOperator_test hΩ hUΩ Q B hQ hB (fun p ↦ (f.chart p).index) _ _ ht
    u φ hφ hc hs j

/-- The SAME finite solver uses the physical plus-pairing convention. Its
right-hand side pairs the full source-plus-residual operator, so it does not
replace the angular source by I or discard its low-frequency complement
(`real-sector-normalization`, `prop:complete-residual`). -/
theorem selectedFiniteDirectSolver_physicalPair_test_of_commonCharts
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L)
    (hΩ : IsOpen Ω) {U : Set E} (hUΩ : U ⊆ Ω)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (R C : Fin 2 → f.centers → ℝ)
    (hb : ∀ o p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B o)) (R o p) (C o p))
    (Op : Fin 2 → f.centers → H →L[ℂ] H)
    (ht : ∀ p u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ physicalCoordinates (f.chart p).index ⁻¹' U → ∀ j,
      physicalTestAction (coefficient (f.chart p).index Q) (zeroth (f.chart p).index B)
        (fun y ↦ (selectedCommonChartSolver f p L Q B output ho hob hib (Op 0 p) u y).ofLp)
        φ j = ∫ y, φ y •
          ((maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
            (selectedSourceSymbol f p (2*L)) +
            selectedCommonChartResidual f p L Q B (W₁ p) output ho hob hib (Op 1 p)) u) y j) :
    let retarded := fun o : Fin 2 ↦ (sourceCutMultiplier output ho hob).comp
      ((finitePhysicalOperator (fun p ↦ (f.chart p).index) (Op o)).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
    let S := selectedFiniteDirectSolver f L Q B output ho hob (retarded 0)
    let Efull := selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1)
    ∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ j,
      physicalTestAction
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (physicalPairedSectorSum {()} (fun _ : Unit ↦ S) u y).ofLp) φ j =
        ∫ y, φ y • (physicalPairedSectorSum {()} (fun _ : Unit ↦ 1 + Efull) u) y j := by
  intro retarded S Efull u φ hφ hc hs j
  have hS := selectedFiniteDirectSolver_eq_commonChartSum f L Q B output ho hob hib hsupp
    (R 0) (C 0) (hb 0) (Op 0)
  have hT := selectedFiniteCompleteError_eq_commonChartSum f L hL Q B W₁ output ho hob hib hsupp
    (R 1) (C 1) (hb 1) (Op 1)
  change S = _ at hS
  change 1 + Efull = _ at hT
  rw [hS, hT]
  exact finitePhysicalOperator_physicalPair_test hΩ hUΩ Q B hQ hB
    (fun p ↦ (f.chart p).index) _ _ ht u φ hφ hc hs j

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
