module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SelectedGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.SourceInverse
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.Geometry

/-!
# Actual source geometry on the selected coefficient domain

Transfer the finite incidence producer's literal current inverse to the
normalized source using Hamilton matching on the original coefficient
domain. The prescribed mask, common target and local inverse range are
unchanged. No new local cone or independent inverse is chosen.
-/

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic NormalizedSelection FrozenModel RetainedFrozen
open ContinuumNormalReduction.TransportSymbol
open CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.RetainedRowGeometry

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The original retained coefficient-domain inclusion suffices to identify
the current augmented transport, its full differential and its literal
Jacobian with the normalized source on the WHOLE original carrier cone.
Only convexity of the physical ball is used for the segment containment;
no extra relation between the physical and angular radii is imposed.
Consumer: `retained_source_canonical_comparison_geometry`
(`app:ch_background:eq:bg-Nsigma`, `bg-Psi`, `bg-jacobian`). -/
theorem source_transport_on_retained_coefficient_domain
    {c C : ℝ} (hP : P.IsValid c C)
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
    {R : ℝ} (hRT : R ≤ T.physicalRadius)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (houter : coefficientDomain zRoot r a ⊆ ball (0 : Euclidean n) R ×ˢ V) :
    EqOn (augmentedTransportGradient (transportPosition T Qσ))
      (augmentedTransportGradient (normalizedTransportPosition T Q₀ σ))
      (symbolInputDomain zRoot ηb r a) ∧
    EqOn (fderiv ℝ (augmentedTransportGradient (transportPosition T Qσ)))
      (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q₀ σ)))
      (symbolInputDomain zRoot ηb r a) ∧
    EqOn (transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Qσ))
      (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q₀ σ))
      (symbolInputDomain zRoot ηb r a) := by
  let E := ball (0 : Euclidean n) R ×ˢ V
  have hmatch : EqOn (transportPosition T Qσ) (normalizedTransportPosition T Q₀ σ) E := by
    have hh := (SourceMatching.current_transportPosition_source_dilation_on_patch
      T Q₀ Qσ hF hrank hphysical hseed htrans hσ hσ1 hscaled).1
    exact fun p hp ↦ hh ⟨ball_subset_ball hRT hp.1,
      fun j ↦ (hVP hp.2 j).trans (by linarith only [hP.1])⟩
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1,
      MapsTo (transportSegmentInput n t) (symbolInputDomain zRoot ηb r a) E := by
    intro t ht p hp
    apply houter
    refine ⟨?_, hp.2.1, hp.1.1⟩
    have hh := (convex_ball (0 : Euclidean n) a) hp.1.2.2 hp.1.2.1
      (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
    have he : (1 - t) • p.1.2 + t • p.1.1 = p.1.2 + t • (p.1.1 - p.1.2) := by module
    change p.1.2 + t • (p.1.1 - p.1.2) ∈ ball (0 : Euclidean n) a
    exact he ▸ hh
  have haug := retained_augmentedTransport_eqOn_of_matching (isOpen_ball.prod hV)
    hmatch (symbolInputDomain_open zRoot ηb r a) hseg
  exact ⟨haug.1, haug.2, source_transportAbsoluteJacobian_eqOn_of_matching
    (adaptedSliceCoordinates T) (isOpen_ball.prod hV) hmatch
      (symbolInputDomain_open zRoot ηb r a) hseg⟩

/-- Apply the retained current spectral geometry and its normalized inverse
range to the actual source on the SAME common cone. Smoothness, the true
source inverse equation, differential/Jacobian gaps, full radial range,
Jacobian regularity/scaling and the closed supported shell are conclusions.
The hypotheses are the geometric outputs of
`NormalizedSelection.exists_finite_incidence_comparison_inputs` and the
original coefficient-domain inclusion; no convergence or normal bound is
assumed. Consumers: the positive branch of `hfamily`/`hglobal` in
`exists_source_family_controlled_half_gap` and the literal normal identity in
`retained_source_normal_eq_normalized_on_common_cone`
(`app:ch_background:prop:bg-normalized`, `bg-Psi`, `bg-jacobian`). -/
theorem retained_source_canonical_comparison_geometry
    {c C : ℝ} (hP : P.IsValid c C)
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
    {R : ℝ} (hRT : R ≤ T.physicalRadius)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' b gap : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hb : 0 < b)
    (houter : coefficientDomain zRoot r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (hgeometry : RetainedSpectralGeometry T Qσ zRoot ηb r a)
    {K W : Set (InputVariables n)} {Qc Ω : Set (Variables n × Euclidean 2)}
    (hKW : K ⊆ W) (hWinput : W ⊆ symbolInputDomain zRoot ηb r (6 * a))
    (hQc : IsCompact Qc) (hQcΩ : Qc ⊆ Ω)
    (hΩinput : Ω ⊆ symbolDomain T Qσ zRoot ηb r (6 * a))
    (hne : ∀ q ∈ Ω, q.1.2.2 ≠ 0)
    (hcone : ∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ω ↔ q ∈ Ω)
    (hrange : MapsTo (inverseCoordinates (symbolInverse T Qσ zRoot ηb r (6 * a))) Qc K)
    (hnormalized : MapsTo (fun q ↦ inverseCoordinates (symbolInverse T Qσ zRoot ηb r (6 * a))
      (normalizeOutputRadius b q)) Ω K)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (hhalf : ∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
      (fderiv ℝ (augmentedTransportGradient (transportPosition T Qσ)) p) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)
    (hgap : ∀ p ∈ K, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
      (transportPosition T Qσ) p)
    (hmask : ∀ p ∈ conicMaskSupport zRoot ηb r' a', normalizeOutputRadius b
      (augmentedTransportGradient (transportPosition T Qσ) p) ∈ Qc) :
    let Z := normalizedTransportPosition T Q₀ σ
    let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) Z
    let u := symbolInverse T Qσ zRoot ηb r (6 * a)
    ContDiffOn ℝ ∞ (augmentedTransportGradient Z) (radialInputDomain W) ∧
    ContDiffOn ℝ ∞ u Ω ∧ MapsTo (inverseCoordinates u) Qc K ∧
    MapsTo (inverseCoordinates u) Ω (radialInputDomain W) ∧
    (∀ q ∈ Ω, transportAveragedGradient Z (inverseCoordinates u q) = q.1.2.2) ∧
    (∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
      (fderiv ℝ (augmentedTransportGradient Z) p) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
    (∀ p ∈ K, gap ≤ J p) ∧
    ContDiffOn ℝ ∞ J (radialInputDomain W) ∧
    (∀ p ∈ radialInputDomain W, 0 < J p) ∧
    EqOn (symbolJacobian T Qσ) J (radialInputDomain W) ∧
    (∀ t : ℝ, 0 < t → ∀ q,
      u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
    (∀ t : ℝ, 0 < t → ∀ q ∈ Ω,
      J (scaleInput t (inverseCoordinates u q)) = t * J (inverseCoordinates u q)) ∧
    (closure (augmentedTransportGradient Z '' conicMaskSupport zRoot ηb r' a') ∩
      {q | q.1.2.2 ≠ 0} ⊆ Ω) ∧
    ∀ q ∈ closure (augmentedTransportGradient Z '' conicMaskSupport zRoot ηb r' a'),
      ‖q.1.2.2‖ = b → q ∈ Qc := by
  intro Z J u
  obtain ⟨hforward, hdifferential, hJac⟩ := source_transport_on_retained_coefficient_domain
    T Q₀ Qσ hP hF hrank hphysical hseed htrans hσ hσ1 hscaled hRT hV hVP houter
  obtain ⟨_, _, G, β, cJ, V₀, L₀, hcJ, _, hLV, hf, hInv, htransverse, _⟩ := hgeometry
  have hradial := radialInputDomain_subset_symbolInputDomain hWinput
  have huScale := symbolInverse_scale_all T Qσ hηb hr hInv htransverse
  have huRadial := inverseCoordinates_mapsTo_radialInputDomain_of_normalized_range hb hne
    (hnormalized.mono_right hKW) (fun t ht q _ ↦ huScale t ht q)
  have huInput := (symbolInverse_maps T Qσ hηb hr hInv htransverse).mono_left hΩinput
  have hsourceForward : ContDiffOn ℝ ∞ (augmentedTransportGradient Z)
      (symbolInputDomain zRoot ηb r (6 * a)) := by
    have hg := transportAveragedGradient_smooth_on_symbolInputDomain T Qσ hηb hr hf
    exact ((contDiffOn_fst.fst.prodMk (contDiffOn_fst.snd.prodMk hg)).prodMk
      contDiffOn_snd.fst.snd).congr (fun p hp ↦ (hforward hp).symm)
  have hsourceJ : ContDiffOn ℝ ∞ J (symbolInputDomain zRoot ηb r (6 * a)) :=
    (transportAbsoluteJacobian_smooth T Qσ hηb hr hf hInv htransverse hcJ).congr
      (fun p hp ↦ (hJac hp).symm)
  change EqOn (transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Qσ))
    J (symbolInputDomain zRoot ηb r (6 * a)) at hJac
  have hmaskInput : conicMaskSupport zRoot ηb r' a' ⊆
      symbolInputDomain zRoot ηb r (6 * a) :=
    (conicMaskSupport_subset hηb hr' ha' har').trans
      (symbolInputDomain_mono zRoot ηb hrr (mul_le_mul_of_nonneg_left haa (by norm_num)))
  have hsourceMask : ∀ p ∈ conicMaskSupport zRoot ηb r' a',
      normalizeOutputRadius b (augmentedTransportGradient Z p) ∈ Qc := by
    intro p hp
    rw [← hforward (hmaskInput hp)]
    exact hmask p hp
  obtain ⟨hpunctured, hshell⟩ :=
    transport_mask_closure_geometry_of_normalized_image hb hQc hQcΩ hcone hsourceMask
  refine ⟨hsourceForward.mono hradial,
    (symbolInverse_smooth T Qσ hηb hr hInv htransverse hLV).mono hΩinput,
    hrange, huRadial, ?_, ?_, ?_, hsourceJ.mono hradial, ?_, ?_, huScale, ?_, hpunctured, hshell⟩
  · intro q hq
    have hgrad := congrArg (fun p : Variables n × Euclidean 2 ↦ p.1.2.2)
      (hforward (huInput hq))
    exact hgrad.symm.trans (transportAveragedGradient_symbolInverse T Qσ hηb hr hInv
      htransverse (hΩinput hq))
  · intro p hp
    rw [← hdifferential (hWinput (hKW hp))]
    exact hhalf p hp
  · intro p hp
    rw [← hJac (hWinput (hKW hp))]
    exact hgap p hp
  · intro p hp
    rw [← hJac (hradial hp)]
    exact transportAbsoluteJacobian_pos T Qσ hηb hr hf hInv htransverse hcJ (hradial hp)
  · intro p hp
    exact (symbolJacobian_eq_actual T Qσ hηb hr hf (hradial hp)).trans (hJac (hradial hp))
  · intro t ht q hq
    have hinput := huInput hq
    have hscaledInput : scaleInput t (inverseCoordinates u q) ∈
        symbolInputDomain zRoot ηb r (6 * a) :=
      ⟨hinput.1, radialScale_mem_supportedCone hinput.2 ht⟩
    rw [← hJac hscaledInput, ← hJac hinput]
    exact transportAbsoluteJacobian_scaling T Qσ hηb hr hf hInv htransverse hinput ht

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
