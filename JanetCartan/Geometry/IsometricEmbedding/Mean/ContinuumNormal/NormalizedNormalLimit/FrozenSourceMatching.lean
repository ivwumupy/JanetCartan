module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.RetainedFrozenGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.Coefficients

/-!
# Exact frozen geometry of the same positive source family

Positive source dilation preserves the physical covector at zero and hence
its entire zero-scale transport. This transports the selected frozen conic
geometry back to the original supplied seed, without choosing another seed,
mask or reference and without an additional comparison threshold for the
unscaled seed.
-/

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic FrozenModel
open ContinuumNormalReduction.TransportSymbol
open CarrierVariation.FamilyInputs NormalizedBackground.SourceGeometry HamiltonPhase
variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
include hF hrank hphysical hseed htrans hσ hσ1 hscaled

/-- The original Hamilton matching proves equality of the seed covectors at
physical zero on the SAME open covector target. The source derivative cancels
the positive scale. Consumer: `normalized_zero_transport_eq_of_source_dilation`
(`app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`). -/
theorem seedCovector_eq_of_source_dilation
    {ζ : Euclidean (n - 1)} (hζ : ((0 : Euclidean n), (0, ζ)) ∈ T.target) :
    seedCovector T Qσ ζ = seedCovector T Q₀ ζ := by
  have hphase := (SourceMatching.projected_current_chart_source_dilation
    T Q₀ Qσ hF hrank hphysical hseed htrans hσ hσ1 hscaled).2.1
  have hn : ∀ᶠ x : Euclidean n in 𝓝 0, (x, (0, ζ)) ∈ T.target :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      ((T.currentChart Q₀).isOpen_target.mem_nhds hζ)
  have heq : (fun x ↦ T.zeroEnergyPhase Qσ (x, ζ)) =ᶠ[𝓝 0]
      (fun x ↦ sourcePhase (T.zeroEnergyPhase Q₀) σ (x, ζ)) := by
    filter_upwards [hn] with x hx
    exact hphase hx
  have hd : DifferentiableAt ℝ (fun x ↦ T.zeroEnergyPhase Q₀ (x, ζ)) (σ • (0 : Euclidean n)) := by
    simp only [smul_zero]
    exact ((T.currentChart Q₀).hasFDerivAt_phase hζ).differentiableAt.comp 0
      (differentiableAt_id.prodMk (differentiableAt_const (0, ζ)))
  simpa only [seedCovector, smul_zero] using
    heq.gradient_eq.trans (gradient_sourcePhase_position hσ.ne' hd)

/-- The canonical zero-scale transport is invariant under positive source
dilation. Equality holds for every physical position, while the original
carrier labels remain fixed. Consumer: transfer of the selected frozen conic
geometry to the supplied seed (`app:ch_background:eq:bg-Psi`, `bg-Nsigma`). -/
theorem normalized_zero_transport_eq_of_source_dilation
    {p : Euclidean n × CarrierParameter}
    (hp : ((0 : Euclidean n), (0, T.reference.spatialPatch (parameter p.2))) ∈ T.target) :
    normalizedTransportPosition T Qσ 0 p = normalizedTransportPosition T Q₀ 0 p := by
  have hn : ∀ᶠ ζ : Euclidean (n - 1) in 𝓝 (T.reference.spatialPatch (parameter p.2)),
      ((0 : Euclidean n), (0, ζ)) ∈ T.target :=
    (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt.preimage_mem_nhds
      ((T.currentChart Q₀).isOpen_target.mem_nhds hp)
  apply Filter.EventuallyEq.gradient_eq
  filter_upwards [hn] with ζ hζ
  rw [normalizedPhase_zero, normalizedPhase_zero,
    seedCovector_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical hseed htrans hσ hσ1 hscaled hζ]

/-- Exact zero-scale forward geometry of the SAME source seed (bg-Nsigma, bg-Psi). -/
theorem source_frozen_transport_geometry_eq
    {c C : ℝ} (hP : P.IsValid c C)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hr : 0 < r) (har : a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter zRoot) (3 * r) ×ˢ closedBall (zRoot 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    let Z₀ := normalizedTransportPosition T Q₀ 0
    let Zσ := normalizedTransportPosition T Qσ 0
    let W := frozenInputDomain zRoot ηb r a
    EqOn (augmentedTransportGradient Zσ) (augmentedTransportGradient Z₀) W ∧
    EqOn (fderiv ℝ (augmentedTransportGradient Zσ))
      (fderiv ℝ (augmentedTransportGradient Z₀)) W ∧
    EqOn (transportAbsoluteJacobian (adaptedSliceCoordinates T) Zσ)
      (transportAbsoluteJacobian (adaptedSliceCoordinates T) Z₀) W := by
  intro Z₀ Zσ W
  let E : Set (Euclidean n × CarrierParameter) :=
    univ ×ˢ (parameter ⁻¹' parameterInterior (2 * P.radius))
  have hE : IsOpen E := isOpen_univ.prod ((isOpen_parameterInterior _).preimage parameter.continuous)
  have hmatch : EqOn Zσ Z₀ E := by
    intro p hp
    exact normalized_zero_transport_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical hseed htrans
      hσ hσ1 hscaled (T.target_contains_closed (mem_ball_self T.physicalRadius_pos)
        (fun j ↦ (hp.2 j).le))
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W E := by
    intro t _ p hp
    exact ⟨mem_univ _, fun j ↦
      (carrierInterior_of_frozenInputDomain hr har hcarrier hp j).trans (by linarith [hP.1])⟩
  have haug := retained_augmentedTransport_eqOn_of_matching hE hmatch
    (frozenInputDomain_open ..) hseg
  exact ⟨haug.1, haug.2,
    source_transportAbsoluteJacobian_eqOn_of_matching
      (adaptedSliceCoordinates T) hE hmatch (frozenInputDomain_open ..) hseg⟩

/-- The original annular charts agree at physical zero under source dilation
(bg-Psi). This compares the entire original label interval. -/
theorem source_adaptedTransportChart_origin_eq
    {c C : ℝ} (hP : P.IsValid c C)
    {zRoot : Euclidean 3} {r a : ℝ} (har : a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter zRoot) (3 * r) ×ˢ closedBall (zRoot 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {v : Euclidean 2} (hv : v ∈ ball (spectatorCenter zRoot) a)
    {u : ℝ × Euclidean (n - 1)} (hu : u.1 ∈ closedBall (zRoot 0) (3 * r)) :
    adaptedTransportChart T Qσ (v, 0, 0) u = adaptedTransportChart T Q₀ (v, 0, 0) u := by
  have hz : parameter (u.1, v) ∈ parameterInterior (3 * P.radius / 2) :=
    hcarrier ⟨closedBall_subset_closedBall har (ball_subset_closedBall hv), hu⟩
  have hphase := spatialPatch_mem_phaseBuffer T hP (fun j ↦ (hz j).le)
  have heq : (fun x ↦ normalizedTransportPosition T Qσ 0 (x, (u.1, v))) =
      (fun x ↦ normalizedTransportPosition T Q₀ 0 (x, (u.1, v))) := by
    funext x
    apply normalized_zero_transport_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical hseed htrans hσ hσ1 hscaled
    exact T.target_contains_closed (mem_ball_self T.physicalRadius_pos)
      (fun j ↦ (hz j).le.trans (by linarith [hP.1]))
  have hgrad : transportAveragedGradient (normalizedTransportPosition T Qσ 0)
      ((0, 0), (u.1, v), u.2) =
      transportAveragedGradient (normalizedTransportPosition T Q₀ 0) ((0, 0), (u.1, v), u.2) := by
    have hinner : (fun x ↦ inner ℝ (normalizedTransportPosition T Qσ 0 (x, (u.1, v))) u.2) =
        (fun x ↦ inner ℝ (normalizedTransportPosition T Q₀ 0 (x, (u.1, v))) u.2) :=
      funext (fun x ↦ congrArg (fun y ↦ inner ℝ y u.2) (congrFun heq x))
    unfold transportAveragedGradient
    apply intervalIntegral.integral_congr
    intro t _
    exact congrArg (fun f : Euclidean n → ℝ ↦ gradient f (0 + t • (0 - 0))) hinner
  have hs := transportAveragedGradient_zero_eq_origin T Qσ ((0, 0), (u.1, v), u.2) hphase
  have h0 := transportAveragedGradient_zero_eq_origin T Q₀ ((0, 0), (u.1, v), u.2) hphase
  exact congrArg (fun w ↦ (physicalCoordinates T w).ofLp) (hs.symm.trans (hgrad.trans h0))

/-- The same full frozen conic domain survives positive source dilation
(bg-full-complex-amplitude). No inverse or new mask is selected. -/
theorem frozenSymbolDomain_eq_of_source_dilation
    {c C : ℝ} (hP : P.IsValid c C)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hr : 0 < r) (har : a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter zRoot) (3 * r) ×ˢ closedBall (zRoot 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    frozenSymbolDomain T Qσ zRoot ηb r a = frozenSymbolDomain T Q₀ zRoot ηb r a := by
  ext p
  change (symbolOutputCoordinates T (originOutput p) ∈ supportedOutput T Qσ zRoot ηb r a) ↔
    symbolOutputCoordinates T (originOutput p) ∈ supportedOutput T Q₀ zRoot ηb r a
  have he (hv : p.2 ∈ ball (spectatorCenter zRoot) a)
      (u : ℝ × Euclidean (n - 1))
      (hu : u ∈ supportedCone zRoot
        (NormedSpace.normalize ηb) r (angularWidth ηb r)) :=
    source_adaptedTransportChart_origin_eq T Q₀ Qσ hF hrank hphysical hseed htrans hσ hσ1 hscaled
      hP har hcarrier hv (closedBall_subset_closedBall (by linarith : r ≤ 3 * r)
        (ball_subset_closedBall hu.1))
  constructor
  · rintro ⟨hp, u, hu, heq⟩
    exact ⟨hp, u, hu, (he hp.1 u hu).symm.trans heq⟩
  · rintro ⟨hp, u, hu, heq⟩
    exact ⟨hp, u, hu, (he hp.1 u hu).trans heq⟩


/-- The SAME globally zero-extended canonical frozen inverse agrees after
source dilation. Annular injectivity proves agreement of the inverse choices
on the unchanged conic image (bg-Psi, bg-full-complex-amplitude). -/
theorem frozenSymbolInverse_eq_of_source_dilation
    {c C : ℝ} (hP : P.IsValid c C)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (hgeometry : RetainedFrozen.RetainedSpectralGeometry T Qσ zRoot ηb r a) :
    frozenSymbolInverse T Qσ zRoot ηb r (6 * a) =
      frozenSymbolInverse T Q₀ zRoot ηb r (6 * a) := by
  classical
  obtain ⟨har, hcarrier, G, β, cJ, Vi, Li, _, _, hLV, _, hInv, htransverse, _⟩ := hgeometry
  have hdom := frozenSymbolDomain_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical hseed htrans
    hσ hσ1 hscaled hP (ηb := ηb) hr har hcarrier
  funext p
  let q := symbolOutputCoordinates T (originOutput p)
  change conicInverse T Qσ zRoot ηb r (6 * a) q = conicInverse T Q₀ zRoot ηb r (6 * a) q
  by_cases hp : q ∈ supportedOutput T Qσ zRoot ηb r (6 * a)
  · have hp0 : q ∈ supportedOutput T Q₀ zRoot ηb r (6 * a) := by
      change p ∈ frozenSymbolDomain T Q₀ zRoot ηb r (6 * a)
      rw [← hdom]
      exact hp
    rw [conicInverse_eq T Qσ hp, conicInverse_eq T Q₀ hp0]
    let w := (‖ηb‖ / ‖q.2.2‖) • q.2
    have hv := normalizedOutput_mem_inverseRange T Qσ hηb hr hInv htransverse hLV hp
    have heD (v : ℝ × Euclidean (n - 1)) (hv : v ∈ dataSet zRoot ηb (2 * r)) :
        adaptedTransportChart T Qσ q.1 v = adaptedTransportChart T Q₀ q.1 v :=
      source_adaptedTransportChart_origin_eq T Q₀ Qσ hF hrank hphysical hseed htrans
        hσ hσ1 hscaled hP har hcarrier hp.1.1
        (closedBall_subset_closedBall (by linarith : 2 * r ≤ 3 * r) (ball_subset_closedBall hv.1))
    have hvm := hInv.inverse_mem q.1 hp.1 w hv.2
    have hve := hInv.right_inv q.1 hp.1 w hv.2
    have hw0 : w ∈ adaptedTransportChart T Q₀ q.1 '' dataSet zRoot ηb (2 * r) :=
      ⟨phaseChartInverse (adaptedTransportChart T Qσ) (dataSet zRoot ηb (2 * r)) q.1 w,
        hvm, (heD _ hvm).symm.trans hve⟩
    obtain ⟨hwm, hwe⟩ := phaseChartInverse_spec hw0
    have heInv : phaseChartInverse (adaptedTransportChart T Q₀) (dataSet zRoot ηb (2 * r)) q.1 w =
        phaseChartInverse (adaptedTransportChart T Qσ) (dataSet zRoot ηb (2 * r)) q.1 w := by
      calc
        _ = phaseChartInverse (adaptedTransportChart T Qσ) (dataSet zRoot ηb (2 * r)) q.1
            (adaptedTransportChart T Qσ q.1
              (phaseChartInverse (adaptedTransportChart T Q₀) (dataSet zRoot ηb (2 * r)) q.1 w)) :=
          (hInv.left_inv q.1 hp.1 _ hwm).symm
        _ = _ := congrArg (phaseChartInverse (adaptedTransportChart T Qσ)
          (dataSet zRoot ηb (2 * r)) q.1) ((heD _ hwm).trans hwe)
    exact congrArg (ContinuumNormalReduction.ConicChart.radialScale (‖q.2.2‖ / ‖ηb‖)) heInv.symm
  · have hp0 : q ∉ supportedOutput T Q₀ zRoot ηb r (6 * a) := by
      change p ∉ frozenSymbolDomain T Q₀ zRoot ηb r (6 * a)
      rw [← hdom]
      exact hp
    simp only [conicInverse, indicator_of_notMem hp, indicator_of_notMem hp0]


/-- The selected frozen geometry of ONE positive source supplies the complete
zero-scale comparison geometry of the ORIGINAL seed. All inverse, derivative,
Jacobian and complete-support conclusions use the same masks and cone. No
spectral geometry of the unscaled seed is assumed. Consumers: the zero branch
of `exists_source_family_controlled_half_gap_nonneg` and literal zero-limit
normal matching (bg-Nsigma, bg-Psi, bg-jacobian, bg-full-complex-amplitude). -/
theorem retained_seed_frozen_comparison_geometry_of_source
    {c C : ℝ} (hP : P.IsValid c C)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b gap : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (hgeometry : RetainedFrozen.RetainedSpectralGeometry T Qσ zRoot ηb r a)
    {K W Zmask : Set (InputVariables n)} {Qc Ω : Set (Variables n × Euclidean 2)}
    (hKW : K ⊆ W) (hWinput : W ⊆ symbolInputDomain zRoot ηb r (6 * a))
    (hQc : IsCompact Qc) (hQcΩ : Qc ⊆ Ω)
    (hΩinput : Ω ⊆ frozenSymbolDomain T Qσ zRoot ηb r (6 * a))
    (hne : ∀ q ∈ Ω, q.1.2.2 ≠ 0)
    (hcone : ∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ω ↔ q ∈ Ω)
    (hrange : MapsTo (inverseCoordinates (frozenSymbolInverse T Qσ zRoot ηb r (6 * a))) Qc K)
    (hnormalized : MapsTo (fun q ↦ inverseCoordinates (frozenSymbolInverse T Qσ zRoot ηb r (6 * a))
      (normalizeOutputRadius b q)) Ω K)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (hhalf : ∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
      (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Qσ 0)) p) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)
    (hgap : ∀ p ∈ K, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
      (normalizedTransportPosition T Qσ 0) p)
    (hZinput : Zmask ⊆ frozenInputDomain zRoot ηb r (6 * a))
    (hmask : ∀ p ∈ Zmask, normalizeOutputRadius b
      (augmentedTransportGradient (normalizedTransportPosition T Qσ 0) p) ∈ Qc) :
    let Z := normalizedTransportPosition T Q₀ 0
    let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) Z
    let u := frozenSymbolInverse T Q₀ zRoot ηb r (6 * a)
    ContDiffOn ℝ ∞ u Ω ∧ MapsTo (inverseCoordinates u) Qc K ∧
    MapsTo (inverseCoordinates u) Ω (NormalizedSelection.radialInputDomain W) ∧
    (∀ q ∈ Ω, transportAveragedGradient Z (inverseCoordinates u q) = q.1.2.2) ∧
    (∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
      (fderiv ℝ (augmentedTransportGradient Z) p) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
    (∀ p ∈ K, gap ≤ J p) ∧
    ContDiffOn ℝ ∞ J (NormalizedSelection.radialInputDomain W) ∧
    (∀ p ∈ NormalizedSelection.radialInputDomain W, 0 < J p) ∧
    (∀ q ∈ Ω, ‖(u q).2‖ ≤ 2 * ‖q.1.2.2‖) ∧
    (∀ t : ℝ, 0 < t → ∀ q,
      u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
    (∀ t : ℝ, 0 < t → ∀ q ∈ Ω,
      J (scaleInput t (inverseCoordinates u q)) = t * J (inverseCoordinates u q)) ∧
    (closure (augmentedTransportGradient Z '' Zmask) ∩ {q | q.1.2.2 ≠ 0} ⊆ Ω) ∧
    ∀ q ∈ closure (augmentedTransportGradient Z '' Zmask), ‖q.1.2.2‖ = b → q ∈ Qc := by
  intro Z J u
  have hinv := frozenSymbolInverse_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical hseed htrans
    hσ hσ1 hscaled hP hηb hr hgeometry
  obtain ⟨haug, hdifferential, hJac⟩ := source_frozen_transport_geometry_eq
    T Q₀ Qσ hF hrank hphysical hseed htrans hσ hσ1 hscaled hP (ηb := ηb) hr
      hgeometry.1 hgeometry.2.1
  have hradial : NormalizedSelection.radialInputDomain W ⊆ frozenInputDomain zRoot ηb r (6 * a) := by
    intro p hp
    have hinput := radialInputDomain_subset_symbolInputDomain hWinput hp
    exact ⟨⟨hinput.1.1, mem_ball_self (by positivity), mem_ball_self (by positivity)⟩, hinput.2⟩
  have hKfrozen : K ⊆ frozenInputDomain zRoot ηb r (6 * a) :=
    hKW.trans ((NormalizedSelection.subset_radialInputDomain W).trans hradial)
  have hraw := retained_frozen_canonical_comparison_geometry T Qσ hP hηb hr ha hb
    hgeometry hWinput hQc hQcΩ hΩinput hne hcone (hnormalized.mono_right hKW) hmask
  dsimp only at hraw
  rw [hinv] at hraw hrange
  obtain ⟨hu, hmap, heq, hJ, hJpos, _, hupper, hscale, hJscale, _, _⟩ := hraw
  have hmask0 : ∀ p ∈ Zmask, normalizeOutputRadius b (augmentedTransportGradient Z p) ∈ Qc := by
    intro p hp
    exact (congrArg (normalizeOutputRadius b) (haug (hZinput hp))) ▸ hmask p hp
  obtain ⟨hpunctured, hshell⟩ := transport_mask_closure_geometry_of_normalized_image
    hb hQc hQcΩ hcone hmask0
  refine ⟨hu, hrange, hmap, ?_, ?_, ?_,
    hJ.congr (fun p hp ↦ (hJac (hradial hp)).symm), ?_, hupper, hscale, ?_, hpunctured, hshell⟩
  · intro q hq
    exact (congrArg (fun p : Variables n × Euclidean 2 ↦ p.1.2.2)
      (haug (hradial (hmap hq)))).symm.trans (heq q hq)
  · intro p hp
    rw [← hdifferential (hKfrozen hp)]
    exact hhalf p hp
  · intro p hp
    exact (hgap p hp).trans_eq (hJac (hKfrozen hp))
  · intro p hp
    exact (hJpos p hp).trans_eq (hJac (hradial hp))
  · intro t ht q hq
    have hp := hradial (hmap hq)
    have hscaledInput : scaleInput t (inverseCoordinates u q) ∈ frozenInputDomain zRoot ηb r (6 * a) :=
      ⟨hp.1, radialScale_mem_supportedCone hp.2 ht⟩
    exact (hJac hscaledInput).symm.trans ((hJscale t ht q hq).trans
      (congrArg (fun s ↦ t * s) (hJac hp)))

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
