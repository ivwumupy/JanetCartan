module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.PdoIdentification
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.PdoMasks

/-!
# Plateaux for the selected finite operators

Position multipliers absorb a cutoff which is one on their full support.
The existing literal PDO test-realization theorem supplies source absorption;
the coordinate conjugations below preserve the side of every multiplier.
Consumers: the direct solver and three-term residual in `Support`, for
`sector-theorem-solution`, `sector-theorem-residual`, and `measured-adjoint`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open Characteristic.PdoRealization FiniteEvolution FiniteAlgebraic FinitePdo
open FiniteMasks FiniteMasks.ActualFamily FourierIntegral LowBounds Pseudodifferential
open JanetCartan.CharacteristicTransport.CompleteResidual
open ArbitraryAccuracy.ResidualLocalization
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d q
local notation "CMat" => Matrix (Fin q) (Fin q) ℂ

/-- A real cutoff equal to one on the old mask's support absorbs on both
sides. This uses no idempotence of the old mask (`measured-adjoint`). -/
theorem sourceCutMultiplier_plateau_comp
    (a χ : E → ℝ) (ha : Continuous a) (hχ : Continuous χ)
    (hab : ∀ y, ‖a y‖ ≤ 1) (hχb : ∀ y, ‖χ y‖ ≤ 1)
    (hp : ∀ y ∈ tsupport a, χ y = 1) :
    (sourceCutMultiplier (r := q) a ha hab).comp (sourceCutMultiplier χ hχ hχb) =
        sourceCutMultiplier a ha hab ∧
      (sourceCutMultiplier (r := q) χ hχ hχb).comp (sourceCutMultiplier a ha hab) =
        sourceCutMultiplier a ha hab := by
  have he (y : E) : (a y : ℂ) * (χ y : ℂ) = (a y : ℂ) := by
    by_cases hy : a y = 0
    · simp [hy]
    · simp [hp y (subset_tsupport a hy)]
  have hs : (sourceCutMultiplier (r := q) a ha hab).comp
      (sourceCutMultiplier χ hχ hχb) = sourceCutMultiplier a ha hab := by
    ext1 u
    apply Lp.ext
    filter_upwards [sourceCutMultiplier_coeFn a ha hab (sourceCutMultiplier χ hχ hχb u),
      sourceCutMultiplier_coeFn χ hχ hχb u, sourceCutMultiplier_coeFn a ha hab u]
      with y hy hχy hay
    change sourceCutMultiplier a ha hab (sourceCutMultiplier χ hχ hχb u) y = _
    rw [hy, hχy, hay, smul_smul, he]
  refine ⟨hs, ?_⟩
  simpa only [ContinuousLinearMap.adjoint_comp, sourceCutMultiplier_adjoint] using
    congrArg ContinuousLinearMap.adjoint hs

/-- The right physical multiplier pulls back to the right chart multiplier.
Consumer: source absorption of the selected PDO sums (`measured-adjoint`). -/
theorem physicalOperator_comp_sourcePlateau
    (i : Fin (d+1)) (χ : E → ℝ) (hχ : Continuous χ) (hb : ∀ y, ‖χ y‖ ≤ 1)
    (T : H →L[ℂ] H) :
    (physicalOperator i T).comp (sourceCutMultiplier χ hχ hb) =
      physicalOperator i (T.comp (sourceCutMultiplier (χ ∘ physicalCoordinates i)
        (hχ.comp (physicalCoordinates i).continuous) (fun _ ↦ hb _))) := by
  ext1 u
  simp only [ContinuousLinearMap.comp_apply, physicalOperator_apply,
    physicalPullbackL2_sourceCutMultiplier]

variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- The original input mask, pulled back to any retained chart, absorbs the
fixed physical source plateau. The existing literal PDO realization/density
proof is reused (`energy-complete-residual`). -/
theorem selectedChartPDO_source_plateau
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (χout : E → ℂ) (c : E → E → CMat)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hb : ∀ y, ‖χ y‖ ≤ 1)
    (hp : ∀ y ∈ tsupport f.inputMask, χ y = 1) :
    (physicalOperator (f.chart p).index (maskedPhysicalPDO χout (chartInputMask f p) c)).comp
      (sourceCutMultiplier χ hχ.continuous hb) =
        physicalOperator (f.chart p).index (maskedPhysicalPDO χout (chartInputMask f p) c) := by
  rw [physicalOperator_comp_sourcePlateau]
  congr 1
  apply (maskedPhysicalPDO_plateau_identities χout (chartInputMask f p) c
    (fun _ ↦ 1) (χ ∘ physicalCoordinates (f.chart p).index)
    continuous_const (hχ.comp (physicalCoordinates (f.chart p).index).contDiff)
    (by simp) (fun _ ↦ hb _) (fun _ _ ↦ rfl) ?_).2
  intro y hy
  apply hp
  exact tsupport_comp_subset Complex.ofReal_zero f.inputMask
    (tsupport_comp_subset_preimage (fun z ↦ (f.inputMask z : ℂ))
      (physicalCoordinates (f.chart p).index).continuous hy)

/-- A common-output chart PDO has the full common output support. The graph
certificate is the first field of the retained `EndpointPdoEstimates`;
no smaller measurement plateau is asserted (`sector-theorem-residual`). -/
theorem selectedChartPDO_output_plateau
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (c : E → E → CMat) (R C : ℝ)
    (hgraph : GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (endpointOutputMask f p output) (chartInputMask f p) c) R C)
    (ψ : E → ℝ) (hψ : Continuous ψ) (hb : ∀ y, ‖ψ y‖ ≤ 1)
    (hp : ∀ y ∈ tsupport output, ψ y = 1) :
    (sourceCutMultiplier ψ hψ hb).comp
      (physicalOperator (f.chart p).index
        (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p) c)) =
      physicalOperator (f.chart p).index
        (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p) c) := by
  rw [sourceCutMultiplier_comp_physicalOperator,
    sourceCutMultiplier_comp_maskedPhysicalPDO _ _ _ _ _ _ R C hgraph]
  congr 2
  funext y
  change (ψ (physicalCoordinates (f.chart p).index y) : ℂ) *
    (output (physicalCoordinates (f.chart p).index y) : ℂ) =
      (output (physicalCoordinates (f.chart p).index y) : ℂ)
  by_cases hy : output (physicalCoordinates (f.chart p).index y) = 0
  · simp [hy]
  · simp [hp _ (subset_tsupport output hy)]

end JanetCartan.RegularSector.FiniteAssembly
