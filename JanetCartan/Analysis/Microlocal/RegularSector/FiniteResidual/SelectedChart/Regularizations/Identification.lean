module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Masks

/-!
# Identification with the same retained retarded operators

The canonical retarded test action is constructed in `Regularizations.Chart`.
The retained operator's action comes from `SelectedChartEvolutionAt`. The
common physical masks supplied by `PhysicalConstruction` make those actions
identical; density then identifies the bounded operators and their adjoints.
Source: `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.SelectedChart
open Characteristic Characteristic.ResidualCoordinates Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.UncutTestAction
open FourierIntegral FourierIntegral.LowBounds
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
variable {d q : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d q

/-- The canonical operator with the ORIGINAL chart masks and the SAME
retained operator agree after the actual common localization. The canonical
test action is an output of `exists_selected_supported_graph_regularizations`;
`hOp` and the two absorption equalities are outputs of
`exists_finite_physical_evolution_data`. Density identifies operators, retaining
source multiplication before Fourier multiplication (`energy-complete-residual`). -/
theorem retained_common_localization_eq_canonical
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
    (Δ a : ℝ) (Ψ : TwoTimePhase d) (W : TwoTimeAmplitude d q) (β : E → ℂ)
    (canonical : H →L[ℂ] H)
    (hcanonical : ∀ u : graphTestSpace (d+1) q,
      canonical (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (retardedPhysicalIntegral Ψ W (chartOutputMask f p) (chartInputMask f p) β
          (chartPhysicalMasks_properties f p).2.1 a u y))
    (χout χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (o : ℕ) (A : ℝ) (As : ℕ → ℝ) (Op : H →L[ℂ] H)
    (hOp : RetainedSignedRetardedBounds (Metric.closedBall x RQ) Q B Δ a Ψ W
      χout χsource β hs o A As Op)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hout : tsupport output ⊆ Metric.ball x f.physicalRadius)
    (hlocalout : ∀ y, (output y : ℂ) * χout ((physicalCoordinates (f.chart p).index).symm y) = (output y : ℂ))
    (hlocalin : ∀ y, χsource ((physicalCoordinates (f.chart p).index).symm y) *
      (f.inputMask y : ℂ) = (f.inputMask y : ℂ)) :
    let e := physicalCoordinates (f.chart p).index
    let Mo := sourceCutMultiplier (r := q) (fun y ↦ output (e y)) (ho.comp e.continuous) (fun y ↦ hob (e y))
    let Mi := sourceCutMultiplier (r := q) (fun y ↦ f.inputMask (e y))
      (f.inputMask_smooth.continuous.comp e.continuous) (fun y ↦ by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (f.inputMask_range (e y)).1]
          using (f.inputMask_range (e y)).2)
    Mo.comp canonical = Mo.comp (Op.comp Mi) := by
  intro e Mo Mi
  let ψout : E → ℝ := fun y ↦ output (e y)
  let ψsource : E → ℝ := fun y ↦ f.inputMask (e y)
  have hsource : ContDiff ℝ ∞ ψsource := f.inputMask_smooth.comp e.contDiff
  have hsb : ∀ y, ‖ψsource y‖ ≤ 1 := fun y ↦ by
    simpa only [ψsource, Real.norm_eq_abs, abs_of_nonneg (f.inputMask_range (e y)).1]
      using (f.inputMask_range (e y)).2
  have hinput : ∀ y, χsource y * (ψsource y : ℂ) = (ψsource y : ℂ) := by
    intro y
    simpa only [e, ψsource, ContinuousLinearEquiv.symm_apply_apply] using hlocalin (e y)
  have houtput : ∀ y, (ψout y : ℂ) * χout y = (ψout y : ℂ) := by
    intro y
    simpa only [e, ψout, ContinuousLinearEquiv.symm_apply_apply] using hlocalout (e y)
  apply DFunLike.coe_injective
  apply denseRange_graphTestToLp.equalizer (Mo.comp canonical).continuous (Mo.comp (Op.comp Mi)).continuous
  funext u
  apply Lp.ext
  have hret := retained_retarded_common_masks_test (Metric.closedBall x RQ) Q B Δ a Ψ W
    χout χsource β hs o A As Op hOp ψout ψsource (ho.comp e.continuous) hsource
    (fun y ↦ hob (e y)) hsb houtput hinput u
  filter_upwards [sourceCutMultiplier_coeFn ψout (ho.comp e.continuous)
    (fun y ↦ hob (e y)) (canonical (graphTestToLp u)), hcanonical u, hret] with y hy hc hr
  change Mo (canonical (graphTestToLp u)) y = Mo (Op (Mi (graphTestToLp u))) y
  change Mo (Op (Mi (graphTestToLp u))) y = _ at hr
  rw [hy, hc, hr]
  apply congrArg (WithLp.toLp 2)
  change (ψout y : ℂ) • retardedPhysicalIntegral Ψ W (chartOutputMask f p)
    (chartInputMask f p) β (chartPhysicalMasks_properties f p).2.1 a u y = _
  unfold retardedPhysicalIntegral
  rw [← mul_smul, commonOutput_mul_chartOutputMask f p output hout y]
  rfl

end JanetCartan.RegularSector.FiniteResidual.SelectedChart
