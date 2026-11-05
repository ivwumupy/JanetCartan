module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.AlgebraicSums
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RetardedSums
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SourceOperator
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.Reality

/-!
# The literal finite direct solver and complete residual

These operators combine the constructed physical retarded, algebraic and
upper-endpoint factors, at the identical enlarged threshold. All source
multipliers stay inside their original factors. The identities here are
operator algebra; the differential equation still requires the selected-chart
tested identity (`energy-complete-residual`, `prop:complete-residual`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic Characteristic.EvolutionIntegral FiniteEvolution FiniteAlgebraic FinitePdo
open FiniteMasks FiniteMasks.ActualFamily FourierIntegral LowBounds
open JanetCartan.CharacteristicTransport.CompleteResidual
open RegularSector.Realization
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- Sum of the SAME retained W₁ upper endpoints, with the common smaller
output mask and the original input mask (`energy-complete-residual`). -/
def selectedFiniteEndpointPDO (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) : H →L[ℂ] H :=
  finitePhysicalOperator (fun p ↦ (f.chart p).index)
    (fun p ↦ maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
      (selectedEndpointSymbol f p L Q (W₁ p)))

/-- The upper-endpoint adjoint reverses every literal chart PDO, including
its physical masks (`measured-adjoint`). -/
theorem selectedFiniteEndpointPDO_adjoint
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) :
    (selectedFiniteEndpointPDO f L Q W₁ output).adjoint =
      finitePhysicalOperator (fun p ↦ (f.chart p).index)
        (fun p ↦ (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointSymbol f p L Q (W₁ p))).adjoint) :=
  finitePhysicalOperator_adjoint _ _

/-- The two-term direct physical solver, before its physical plus pairing.
`retarded` is the already common-masked finite W₀+W₁ operator. The algebraic
term uses the identical `2*L` multiplier; its existing source mask is kept
on the right (`energy-complete-residual`). -/
def selectedFiniteDirectSolver (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retarded : H →L[ℂ] H) : H →L[ℂ] H :=
  retarded + (-Complex.I) • (sourceCutMultiplier output ho hob).comp
    (selectedFiniteAlgebraicPDO f (2*L) Q B 0)

/-- All THREE direct gain-one residual terms: upper endpoint, retarded PW₁,
and full physical derivative of the algebraic inverse. The identity defect
is kept separately below, never omitted (`energy-complete-residual`). -/
def selectedFiniteDirectResidual (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retardedPW₁ : H →L[ℂ] H) : H →L[ℂ] H :=
  selectedFiniteEndpointPDO f L Q W₁ output + retardedPW₁ +
    (-Complex.I) • (sourceCutMultiplier output ho hob).comp
      (selectedFiniteAlgebraicPDO f (2*L) Q B 1)

/-- The literal complete error relative to I, including the same source PDO
and its angular/low-frequency defect. This definition makes no smoothing
claim for `Op(α)-I` (`prop:complete-residual`, `resolved-angular-tail`). -/
def selectedFiniteCompleteError (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retardedPW₁ : H →L[ℂ] H) : H →L[ℂ] H :=
  ((sourceCutMultiplier output ho hob).comp (selectedFiniteSourcePDO f L) - 1) +
    selectedFiniteDirectResidual f L Q B W₁ output ho hob retardedPW₁

/-- The assembled source and three-term residual equal I plus the COMPLETE
error. No differential identity or disappearance of a source cutoff is
asserted by this algebraic identity (`prop:complete-residual`). -/
theorem selectedFiniteCompleteError_identity
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retardedPW₁ : H →L[ℂ] H) :
    (sourceCutMultiplier output ho hob).comp (selectedFiniteSourcePDO f L) +
      selectedFiniteDirectResidual f L Q B W₁ output ho hob retardedPW₁ =
    1 + selectedFiniteCompleteError f L Q B W₁ output ho hob retardedPW₁ := by
  unfold selectedFiniteCompleteError
  abel

/-- Literal adjoint of the two-term physical solver. The new common output
mask moves to the RIGHT of the algebraic adjoint; the imaginary scalar
changes sign (`measured-adjoint`). -/
theorem selectedFiniteDirectSolver_adjoint
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retarded : H →L[ℂ] H) :
    (selectedFiniteDirectSolver f L Q B output ho hob retarded).adjoint =
      retarded.adjoint + Complex.I • (selectedFiniteAlgebraicPDO f (2*L) Q B 0).adjoint.comp
        (sourceCutMultiplier output ho hob) := by
  simp [selectedFiniteDirectSolver, ContinuousLinearMap.adjoint_comp, map_smulₛₗ,
    sourceCutMultiplier_adjoint]

/-- Literal adjoint of all THREE residual contributions, with the same W₁
upper endpoint and full-B algebraic derivative (`measured-adjoint`). -/
theorem selectedFiniteDirectResidual_adjoint
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retardedPW₁ : H →L[ℂ] H) :
    (selectedFiniteDirectResidual f L Q B W₁ output ho hob retardedPW₁).adjoint =
      (selectedFiniteEndpointPDO f L Q W₁ output).adjoint + retardedPW₁.adjoint +
      Complex.I • (selectedFiniteAlgebraicPDO f (2*L) Q B 1).adjoint.comp
        (sourceCutMultiplier output ho hob) := by
  simp [selectedFiniteDirectResidual, ContinuousLinearMap.adjoint_comp, map_smulₛₗ,
    sourceCutMultiplier_adjoint]

/-- Real compression of the constructed physical solver's plus pairing.
This uses S+cSc, with no anti-real normalization (`energy-complete-residual`). -/
def selectedFiniteRealSolver (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retarded : H →L[ℂ] H) :=
  realCompression (physicalPairedSectorSum {()}
    (fun _ : Unit ↦ selectedFiniteDirectSolver f L Q B output ho hob retarded))

/-- The real finite solver's inclusion is the identical physical plus pair
on real L² data. The PDE identity remains the selected-chart assembly's
obligation (`energy-complete-residual`, `real-sector-normalization`). -/
theorem inclusion_selectedFiniteRealSolver
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retarded : H →L[ℂ] H) (u : Lp (EuclideanSpace ℝ (Fin (d+1))) 2 (volume : Measure E)) :
    l2ComplexInclusion volume (selectedFiniteRealSolver f L Q B output ho hob retarded u) =
      physicalPairedSectorSum {()}
        (fun _ : Unit ↦ selectedFiniteDirectSolver f L Q B output ho hob retarded)
        (l2ComplexInclusion volume u) :=
  inclusion_realCompression_physicalPairedSectorSum _ _ _

end JanetCartan.RegularSector.FiniteAssembly
