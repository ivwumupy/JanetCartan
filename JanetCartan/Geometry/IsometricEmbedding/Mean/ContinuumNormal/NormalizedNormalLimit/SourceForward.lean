module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.Forward
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.SourcePhase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RadialInputGeometry

/-!
# Joint source transport regularity on the original retained buffer

The phase's compact scaling buffer is chosen around the entire supplied
physical ball. Every original transport segment and carrier parameter is
retained, and frequency homogeneity extends smoothness to the radial input
domain. The input and output masks are never reselected.
-/

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open ContinuumNormalReduction.TransportSymbol CarrierVariation.FamilyInputs
open NormalizedBackground.SourceGeometry NormalizedSelection

/-- The actual seed phase is jointly smooth in the source scale on the WHOLE
retained input buffer and its radial extension. The cap comes from compact
scaling of the prescribed physical ball, before any density or derivative
order. The segment and parameter containments are exactly those retained by
finite incidence selection and its original coefficient-domain inclusion.
This discharges `hjoint` in the nonnegative full-amplitude and controlled
half-gap comparisons, without constructing a smaller conic inverse
(`app:ch_background:eq:bg-Psi`, `bg-Nsigma`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_source_augmented_smooth_on_retained_buffer
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {c C : ℝ} (hP : P.IsValid c C)
    {R : ℝ} {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    {W : Set (InputVariables n)} (hW : IsOpen W)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hseg : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W (ball 0 R ×ˢ V)) :
    ∃ e > (0 : ℝ), ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (normalizedTransportPosition T Q₀ q.1) q.2)
        (Ioo (-e) e ×ˢ radialInputDomain W) := by
  let ζ := fun z : CarrierParameter ↦ T.reference.spatialPatch (parameter z)
  have hζ : ContDiffOn ℝ ∞ ζ V :=
    (T.reference.spatialPatch_smooth hP).comp parameter.contDiff.contDiffOn
      (fun _ hz j ↦ (hVP hz j).trans_le (by linarith only [hP.1]))
  have hζV : MapsTo ζ V (ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius) :=
    fun _ hz ↦ spatialPatch_mem_phaseBuffer T hP (fun j ↦ (hVP hz j).le)
  obtain ⟨B, hB, hRB, r, hr, hscale⟩ := exists_source_phase_buffer isOpen_ball
    (mem_ball_self T.family.radius_pos) (isCompact_closedBall (0 : Euclidean n) R)
  have hsegments : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W (B ×ˢ V) := by
    intro t ht p hp
    exact ⟨hRB (ball_subset_closedBall (hseg t ht hp).1), (hseg t ht hp).2⟩
  have hjoint := contDiffOn_sourceAugmentedTransport isOpen_ball hB isOpen_ball hV hW
    (zeroEnergyPhase_smooth T Q₀) hζ hζV hscale hIt hIIt hsegments
  change ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
    augmentedTransportGradient (normalizedTransportPosition T Q₀ q.1) q.2)
      (Ioo (-2 * r) (2 * r) ×ˢ W) at hjoint
  refine ⟨2 * r, by positivity, ?_⟩
  simpa only [neg_mul] using
    contDiffOn_augmentedTransport_radialInputDomain isOpen_Ioo hW hjoint

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
