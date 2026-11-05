module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.Hamilton
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.NormalizedTransport
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalCarrier

/-!
# Matching the canonical Hamilton transport and its ambient jets

The row's `CanonicalCarrier.transportPosition` is the canonical covector
derivative of the retained phase. It is not the null-transport ODE footpoint.
For `app:ch_background:eq:bg-Nsigma`, the phase matching is proved from the
actual projected stresses and root/ODE uniqueness, then differentiated on open
buffers. The compact primitive comparison in `FamilyInputs.SourcePrimitives`
is the consumer.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
open HamiltonPhase NormalizedBackground.SourceGeometry
open ActualCarriers CurrentFullPhase ContinuumRow

variable {n N : ℕ} {P : FrozenMenu.Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Match the actual row transport, including all ambient Fréchet jets, to the
integral source extension. The buffers and seed equations precede the scale.
`T.family.phase_smooth` supplies `hS`, and `T.current_section_source` supplies
the seed zero-section containment on a suitably buffered label set. No chart,
trajectory, or transport equality is an input.

Source: `app:ch_background:eq:bg-Nsigma`, `app:ch_background:defn:bg-carriers`.
Consumer: the order `m + 2` primitive difference in `FamilyInputs`. -/
theorem current_transportPosition_source_dilation
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {A B : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    {W : Set (ℝ × Euclidean 2)}
    (hA : IsOpen A) (hc : Convex ℝ A) (hB : IsOpen B) (hV : IsOpen V) (hW : IsOpen W)
    (hS : ContDiffOn ℝ ∞ (fun p : Euclidean n × Euclidean (n - 1) ↦
      phase (T.currentChart Q₀).coordinates (p.1, (0, p.2))) (A ×ˢ V))
    (hsection : ∀ η ∈ V, (0, (0, (0, η))) ∈ (T.currentChart Q₀).source)
    (h0 : (0 : Euclidean n) ∈ A)
    (hlabel : MapsTo (fun z ↦ T.reference.spatialPatch (CanonicalCarrier.parameter z)) W V)
    (htarget : ∀ x ∈ B, ∀ η ∈ V, (x, (0, η)) ∈ T.target)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
    (hmaps : MapsTo (fun x ↦ σ • x) B A) :
    let S := fun p : Euclidean n × Euclidean (n - 1) ↦
      phase (T.currentChart Q₀).coordinates (p.1, (0, p.2))
    let ζ := fun z ↦ T.reference.spatialPatch (CanonicalCarrier.parameter z)
    EqOn (CanonicalCarrier.transportPosition T Qσ) (sourceTransportPosition S ζ σ) (B ×ˢ W) ∧
    ∀ m : ℕ, EqOn (iteratedFDeriv ℝ m (CanonicalCarrier.transportPosition T Qσ))
      (iteratedFDeriv ℝ m (sourceTransportPosition S ζ σ)) (B ×ˢ W) := by
  dsimp only
  have hphase := (projected_current_chart_source_dilation T Q₀ Qσ hF hrank
    hphysical hseed htrans hσ hσ1 hscaled).2.1
  have he : EqOn (CanonicalCarrier.transportPosition T Qσ)
      (sourceTransportPosition
        (fun p ↦ phase (T.currentChart Q₀).coordinates (p.1, (0, p.2)))
        (fun z ↦ T.reference.spatialPatch (CanonicalCarrier.parameter z)) σ) (B ×ˢ W) := by
    intro p hp
    rw [CanonicalCarrier.transportPosition_eq_hamiltonGradient,
      sourceTransportPosition_eq_sourceHamiltonGradient (T.currentChart Q₀)
        (fun z ↦ T.reference.spatialPatch (CanonicalCarrier.parameter z))
        hA hc hV hS hsection h0 hσ.ne' (hmaps hp.1) (hlabel hp.2)]
    apply Filter.EventuallyEq.gradient_eq
    filter_upwards [hV.mem_nhds (hlabel hp.2)] with η hη
    rw [phase_sourceCoordinates]
    exact hphase (htarget p.1 hp.1 η hη)
  refine ⟨he, fun m p hp ↦ ?_⟩
  exact ((eventuallyEq_of_mem ((hB.prod hW).mem_nhds hp)
    (fun q hq ↦ he hq)).iteratedFDeriv ℝ m).eq_of_nhds

/-- A single explicit patch buffer suffices for every positive contracting
scale and every ambient derivative order. Seed phase smoothness, centered
Cauchy data, label containment, and inverse-domain containment are derived
from the retained family. Source: `app:ch_background:eq:bg-Nsigma` and
`app:ch_background:prop:bg-frame`. Consumer: the actual row's primitive
transport comparison on compact subsets of this fixed open buffer. -/
theorem current_transportPosition_source_dilation_on_patch
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ)) :
    let S := fun p : Euclidean n × Euclidean (n - 1) ↦
      phase (T.currentChart Q₀).coordinates (p.1, (0, p.2))
    let ζ := fun z ↦ T.reference.spatialPatch (CanonicalCarrier.parameter z)
    let D := ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (CanonicalCarrier.parameter ⁻¹' FrozenMenu.parameterInterior (2 * P.radius))
    EqOn (CanonicalCarrier.transportPosition T Qσ) (sourceTransportPosition S ζ σ) D ∧
    ∀ m : ℕ, EqOn (iteratedFDeriv ℝ m (CanonicalCarrier.transportPosition T Qσ))
      (iteratedFDeriv ℝ m (sourceTransportPosition S ζ σ)) D := by
  let B := ball (0 : Euclidean n) T.physicalRadius
  let V := ball T.data.adapted.baseData.2.2
    (min T.family.radius (3 * T.family.sourceRadius))
  let W := CanonicalCarrier.parameter ⁻¹' FrozenMenu.parameterInterior (2 * P.radius)
  have hr := T.family.radius_pos
  have hs := T.family.sourceRadius_pos
  have hpr : T.physicalRadius < T.family.radius := by
    have hh := min_le_left T.family.radius (3 * T.family.sourceRadius)
    have hh' := T.physicalRadius_pos
    dsimp [PatchQuantitativeFamily.physicalRadius] at hh' ⊢
    linarith
  have htarget (x : Euclidean n) (hx : x ∈ B) (η : Euclidean (n - 1)) (hη : η ∈ V) :
      (x, (0, η)) ∈ T.target := by
    have hx' : ‖x‖ < T.family.radius := (mem_ball_zero_iff.mp hx).trans hpr
    have hη' : dist η T.data.adapted.baseData.2.2 < T.family.radius :=
      (mem_ball.mp hη).trans_le (min_le_left _ _)
    simpa only [PatchQuantitativeFamily.target, FrozenPhaseReference.AdaptedSection.baseData,
      map_zero, mem_ball, Prod.dist_eq, dist_zero_right, max_lt_iff, dist_self] using
      And.intro hx' (And.intro hr hη')
  have h0 : (0 : Euclidean n) ∈ B := mem_ball_self T.physicalRadius_pos
  have hsection (η : Euclidean (n - 1)) (hη : η ∈ V) :
      (0, (0, (0, η))) ∈ (T.currentChart Q₀).source := by
    have hη' : dist η T.data.adapted.baseData.2.2 < 3 * T.family.sourceRadius :=
      (mem_ball.mp hη).trans_le (min_le_right _ _)
    have hs' : 0 < 3 * T.family.sourceRadius := by positivity
    have hb : (0, (0, (0, η))) ∈
        ball ((0 : ℝ), T.data.adapted.baseData) (3 * T.family.sourceRadius) := by
      simpa only [FrozenPhaseReference.AdaptedSection.baseData, mem_ball,
        Prod.dist_eq, max_lt_iff, dist_self] using ⟨hs', hs', hs', hη'⟩
    have ha := T.family.source_admissible Q₀ hb
    rw [PatchQuantitativeFamily.currentChart,
      restrictChart_source_eq _ _ _ (T.family.source_eq Q₀)]
    refine ⟨hb, ?_⟩
    change ((T.family.flow Q₀).position (0, (0, (0, η))), (0, η)) ∈ T.target
    rw [(T.family.flow Q₀).initial_position _ ha.2, map_zero]
    exact htarget 0 h0 η hη
  have hS : ContDiffOn ℝ ∞ (fun p : Euclidean n × Euclidean (n - 1) ↦
      phase (T.currentChart Q₀).coordinates (p.1, (0, p.2))) (B ×ˢ V) := by
    apply (T.family.phase_smooth Q₀).comp
      (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
    intro p hp
    exact ball_subset_ball (by linarith : T.family.radius ≤ 2 * T.family.radius)
      (htarget p.1 hp.1 p.2 hp.2)
  have hlabel : MapsTo (fun z ↦ T.reference.spatialPatch (CanonicalCarrier.parameter z)) W V := by
    intro z hz
    have hb := T.patch_buffer (CanonicalCarrier.parameter z) (fun i ↦ (hz i).le)
    change (0, T.reference.spatialPatch (CanonicalCarrier.parameter z)) ∈
      ball (0, T.data.adapted.baseData.2.2)
        (min T.family.radius (3 * T.family.sourceRadius)) at hb
    simpa only [V, mem_ball, Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using hb
  have hW : IsOpen W := (FrozenMenu.isOpen_parameterInterior _).preimage
    CanonicalCarrier.parameter.continuous
  apply current_transportPosition_source_dilation T Q₀ Qσ hF hrank hphysical hseed htrans
    isOpen_ball (convex_ball _ _) isOpen_ball isOpen_ball hW hS hsection h0 hlabel htarget
    hσ hσ1 hscaled
  intro x hx
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
  exact (mul_le_of_le_one_left (norm_nonneg x) hσ1).trans_lt (mem_ball_zero_iff.mp hx)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
