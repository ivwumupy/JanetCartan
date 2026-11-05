module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Masks
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Masks

/-!
# The common selected masks in the elapsed integral

The output used by `CompleteFactor` is the actual smaller endpoint output,
and its input is the original chart input. The retained operator has larger
local masks. Their absorption identities, produced by
`exists_finite_direct_operator_bounds`, identify the common localization by
density without moving the input cutoff through the Fourier multiplier.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.UniformEvolution
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo
open RegularSector.FiniteResidual.SelectedChart
open FourierIntegral FourierIntegral.LowBounds
variable {d q : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d q

/-- The actual common output lies in the original chart output carrier.
Consumer: the elapsed-box and time-plateau inputs of
`exists_selected_common_graph_regularizations`
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem endpointOutputMask_tsupport_subset_chartOutputMask
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (hout : tsupport output ⊆ ball x f.physicalRadius) :
    tsupport (endpointOutputMask f p output) ⊆ tsupport (chartOutputMask f p) := by
  intro y hy
  have he := (chartOutputMask_eventuallyEq_one_on_common_output f p output hout hy).eq_of_nhds
  exact subset_tsupport _ (by change chartOutputMask f p y ≠ 0; rw [he]; exact one_ne_zero)

/-- An endpoint-mask retarded realization is exactly the common localization
of the SAME retained operator. The canonical test identity is constructed
in `exists_selected_common_graph_regularizations`; `hOp`, `hlocalout` and
`hlocalin` are retained outputs of `exists_finite_direct_operator_bounds`.
This identifies the operator required by `CompleteFactor`, with the full
original source-before-Fourier ordering (`energy-complete-residual`). -/
theorem retained_common_localization_eq_endpoint
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
    (Δ a : ℝ) (Ψ : TwoTimePhase d) (W : TwoTimeAmplitude d q) (β : E → ℂ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (canonical : H →L[ℂ] H)
    (hcanonical : ∀ u : graphTestSpace (d+1) q,
      canonical (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (retardedPhysicalIntegral Ψ W (endpointOutputMask f p output) (chartInputMask f p) β
          (chartPhysicalMasks_properties f p).2.1 a u y))
    (χout χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (o : ℕ) (A : ℝ) (As : ℕ → ℝ) (Op : H →L[ℂ] H)
    (hOp : RetainedSignedRetardedBounds (closedBall x RQ) Q B Δ a Ψ W
      χout χsource β hs o A As Op)
    (hlocalout : ∀ y, (output y : ℂ) * χout ((physicalCoordinates (f.chart p).index).symm y) =
      (output y : ℂ))
    (hlocalin : ∀ y, χsource ((physicalCoordinates (f.chart p).index).symm y) *
      (f.inputMask y : ℂ) = (f.inputMask y : ℂ))
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) :
    let e := physicalCoordinates (f.chart p).index
    let Mo := sourceCutMultiplier (r := q) (output ∘ e)
      (ho.comp e.continuous) (fun y ↦ hob (e y))
    let Mi := sourceCutMultiplier (r := q) (f.inputMask ∘ e)
      (f.inputMask_smooth.continuous.comp e.continuous) (fun y ↦ hib (e y))
    Mo.comp (Op.comp Mi) = canonical ∧
      Mi.comp (Op.adjoint.comp Mo) = canonical.adjoint := by
  intro e Mo Mi
  have he : Mo.comp (Op.comp Mi) = canonical := by
    apply DFunLike.coe_injective
    apply denseRange_graphTestToLp.equalizer (Mo.comp (Op.comp Mi)).continuous canonical.continuous
    funext u
    apply Lp.ext
    have ht := retained_retarded_common_masks_test (closedBall x RQ) Q B Δ a Ψ W
      χout χsource β hs o A As Op hOp (output ∘ e) (f.inputMask ∘ e)
      (ho.comp e.continuous) (f.inputMask_smooth.comp e.contDiff)
      (fun y ↦ hob (e y)) (fun y ↦ hib (e y))
      (endpointOutputMask_mul_retained_output f p output χout hlocalout)
      (retained_source_mul_chartInputMask f p χsource hlocalin) u
    exact ht.trans (hcanonical u).symm
  refine ⟨he, ?_⟩
  have ha := congrArg ContinuousLinearMap.adjoint he
  simpa only [Mo, Mi, ContinuousLinearMap.adjoint_comp, sourceCutMultiplier_adjoint,
    ContinuousLinearMap.comp_assoc] using ha

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
