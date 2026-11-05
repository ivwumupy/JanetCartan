module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.PdoIdentification.Source

/-!
# Source and algebraic PDO identifications for the direct finite solver

`selectedFiniteSourcePDO_commonOutput` identifies the actual chart source sum
with the masked canonical source at the SAME enlarged threshold `2*L`.
`selectedFiniteAlgebraicPDO_commonOutput` absorbs the actual old output for both
algebraic terms, using the exact per-chart certificates retained by
`exists_finite_algebraic_pdo_sums`. Source certificates are constructed directly
from the actual family. Literal adjoints and the complete identity subtraction
are retained below.

Consumers: `selectedFiniteDirectSolver`, `selectedFiniteDirectResidual`, and
`selectedFiniteCompleteError` (`energy-complete-residual`,
`prop:complete-residual`, `measured-adjoint`). The differential equation and
physical pairing remain with the parent finite assembly.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic Characteristic.EvolutionIntegral Characteristic.PdoRealization
open FiniteEvolution FiniteAlgebraic FinitePdo FiniteMasks FiniteMasks.ActualFamily
open FourierIntegral LowBounds
open JanetCartan.CharacteristicTransport.CompleteResidual
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)

/-- The actual source sum is the terminal angular PDO of the SAME family at
its enlarged threshold, with the common output on the left and the original
source inside (`prop:complete-residual`, `resolved-angular-tail`). -/
theorem selectedFiniteSourcePDO_commonOutput_eq_actualAngularPDO
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hsupp : tsupport output ⊆ ball x f.physicalRadius) :
    finitePhysicalOperator (fun p ↦ (f.chart p).index)
      (fun p ↦ maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
        (selectedSourceSymbol f p (2*L))) =
      (sourceCutMultiplier output ho hob).comp
        (actualAngularPDO (r := d+1) (withEnlargedThreshold f L hL)) := by
  rw [selectedFiniteSourcePDO_commonOutput f L hL output ho hob hsupp,
    selectedFiniteSourcePDO_eq_actualAngularPDO f L hL]

/-- Reverse the literal source chart PDOs and the common output, preserving
all physical masks (`app:ch_regular_base:eq:measured-adjoint`). -/
theorem selectedFiniteSourcePDO_commonOutput_adjoint
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hsupp : tsupport output ⊆ ball x f.physicalRadius) :
    finitePhysicalOperator (fun p ↦ (f.chart p).index)
      (fun p ↦ (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
        (selectedSourceSymbol f p (2*L))).adjoint) =
      (selectedFiniteSourcePDO f L).adjoint.comp (sourceCutMultiplier output ho hob) := by
  rw [← finitePhysicalOperator_adjoint,
    selectedFiniteSourcePDO_commonOutput f L hL output ho hob hsupp,
    ContinuousLinearMap.adjoint_comp, sourceCutMultiplier_adjoint]

/-- The entire identity defect survives the source identification in both
orientations. No angular complement or low-frequency shoulder is discarded
(`prop:complete-residual`, `measured-adjoint`). -/
theorem selectedFiniteSourcePDO_commonOutput_identity_defect
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hsupp : tsupport output ⊆ ball x f.physicalRadius) :
    let T := finitePhysicalOperator (fun p ↦ (f.chart p).index)
      (fun p ↦ maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
        (selectedSourceSymbol f p (2*L)))
    T - 1 = (sourceCutMultiplier output ho hob).comp (selectedFiniteSourcePDO f L) - 1 ∧
      T.adjoint - 1 =
        (selectedFiniteSourcePDO f L).adjoint.comp (sourceCutMultiplier output ho hob) - 1 := by
  dsimp only
  rw [selectedFiniteSourcePDO_commonOutput f L hL output ho hob hsupp,
    ContinuousLinearMap.adjoint_comp, sourceCutMultiplier_adjoint]
  exact ⟨rfl, rfl⟩

/-- The same absorption identity for the literal adjoints of BOTH algebraic
terms. The common output moves to the right, as used by the adjoints of
`selectedFiniteDirectSolver` and `selectedFiniteDirectResidual`
(`app:ch_regular_base:eq:measured-adjoint`). -/
theorem selectedFiniteAlgebraicPDO_commonOutput_adjoint
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1)) (o : Fin 2)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (R C : f.centers → ℝ)
    (hb : ∀ p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B o)) (R p) (C p)) :
    (selectedFiniteAlgebraicPDO f (2*L) Q B o).adjoint.comp
        (sourceCutMultiplier output ho hob) =
      finitePhysicalOperator (fun p ↦ (f.chart p).index)
        (fun p ↦ (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
          (selectedAlgebraicSymbol f p (2*L) Q B o)).adjoint) := by
  rw [← finitePhysicalOperator_adjoint,
    ← selectedFiniteAlgebraicPDO_commonOutput f L Q B o output ho hob hsupp R C hb,
    ContinuousLinearMap.adjoint_comp, sourceCutMultiplier_adjoint]

end JanetCartan.RegularSector.FiniteAssembly
