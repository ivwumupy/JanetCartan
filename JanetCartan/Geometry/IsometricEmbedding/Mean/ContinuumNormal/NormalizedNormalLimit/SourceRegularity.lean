module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SourceAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SmoothAmplitude

/-!
# Regularity of the normalized source amplitudes

Actual coefficient controls and original-domain divided ODE labels give
joint smoothness and the fixed measurement support, including at zero scale.
The conic zero extension retains the whole original detector mask.
-/

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open NullTransport NormalizedBackground.SourceGeometry
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open CarrierVariation CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.PositiveReference
open CarrierVariation.FamilyInputs.WideDensity AmplitudeBound Pseudodifferential PeriodicLocalL2

/-- On the SAME normalized coefficients and original density domain, the
full complex and reflected amplitudes are jointly smooth and supported in
the fixed measurement box for every sufficiently small source scale,
including zero. The source cap precedes the positive density. Smoothness is
derived from the actual coefficient controls, divided ODE-footpoint range,
conic zero extension and spectator integral; it is not a PDO-norm continuity
assertion. Consumer: `exists_source_reflectedPdo_control`, discharging its
PDO smoothness and support inputs. Sources: app:ch_background:prop:bg-normalized,
app:ch_background:eq:bg-full-complex-amplitude and bg-real-symbol. -/
theorem exists_source_fullAmplitudes_contDiff
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {c C : ℝ} (hP : P.IsValid c C) (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hb : ContDiffOn ℝ ∞ (fun q : Euclidean n × CarrierParameter ↦
      carrierScalarAmplitude T Q₀ F row col Φ Y (fun _ ↦ 1) (q.1, parameter q.2) •
        carrierNullvector T Q₀ col (q.1, parameter q.2)) (ball 0 R ×ˢ V))
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (sourceTransportFlow Y σ)) (ball 0 R ×ˢ V)
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (ha : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean (n - 1) ↦ angular p.1 p.2))
    (hh : ContDiff ℝ ∞ high)
    (hhighZero : ∀ r, r ≤ 1 → high r = 0)
    {u : ℝ → Variables n × Euclidean 2 → SliceVariable n}
    {W : Set (InputVariables n)} {Ω : Set (Variables n × Euclidean 2)}
    (hΩ : IsOpen Ω) {sourceCap : ℝ} (hsourceCap : 0 < sourceCap)
    (hend : ∀ side, MapsTo (densityEndpoint side) W D.field.region)
    (hfreqW : ∀ p ∈ W, p.2.2 ≠ 0)
    (Zmask : Set (InputVariables n))
    (hmask : ∀ p ∈ W, FixedCutoffs.physical hr 1 p.1.1 ≠ 0 →
      FixedCutoffs.physical hr 1 p.1.2 ≠ 0 →
      angular p.2.1 (‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Zmask)
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ) (hlow : Cupper * ℓ ≤ 1)
    (hgeometry : ∀ σ ∈ Icc (0 : ℝ) sourceCap,
      let Z := normalizedTransportPosition T Q₀ σ
      let J := transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T) Z
      ContDiffOn ℝ ∞ J W ∧ (∀ p ∈ W, J p ≠ 0) ∧
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Ω W ∧
      (∀ p ∈ Ω, transportAveragedGradient Z (inverseCoordinates (u σ) p) = p.1.2.2) ∧
      (closure (augmentedTransportGradient Z '' Zmask) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) ∧
      (∀ p ∈ Ω, ‖(u σ p).2‖ ≤ Cupper * ‖p.1.2.2‖)) :
    let a := fun σ ↦ coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high σ)
      (FixedCutoffs.physical hr 1)
    let J := fun σ ↦ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T)
      (normalizedTransportPosition T Q₀ σ)
    let foot := fun σ p ↦ sourceDensityFootpointExtension T Y (σ, p)
    ∃ cap > 0, cap ≤ sourceCap ∧ cap ≤ 1 ∧
      ∀ σ ∈ Icc (0 : ℝ) cap, ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), ContDiffAt ℝ ∞ v y) →
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), (1 / 2 : ℝ) ≤ 1 + v y) →
      let av := {(a σ) with normal := fun p ↦ Real.sqrt (1 + v (foot σ p)) • (a σ).normal p}
      ContDiff ℝ ∞ (Function.uncurry (fullComplexMatrixAmplitude av (J σ) (u σ) Ω S)) ∧
      ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude av (J σ) (u σ) Ω S)) ∧
      ∀ ξ i j, SupportedInCenteredBox (4 * r)
        (fun z ↦ fullReflectedMatrixAmplitude av (J σ) (u σ) Ω S ξ z i j) := by
  intro a J foot
  obtain ⟨M, _, sp, hsp, hsp1, _, hcoeff⟩ := exists_normalizedCarrierData_coefficient_controls
    T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high (FixedCutoffs.physical hr 1)
    hP hseed hF hi hrank hR hRT hRU hV hVP hb D hD
    (FixedCutoffs.physical hr 1).contDiff.contDiffOn ha.contDiffOn hh.contDiffOn 0
  let cap := min sp (min sourceCap (min s₀ (1 / 8)))
  have hcap : 0 < cap := lt_min hsp (lt_min hsourceCap (lt_min hs₀ (by norm_num)))
  have hcapsp : cap ≤ sp := min_le_left _ _
  have hcapsource : cap ≤ sourceCap := (min_le_right _ _).trans (min_le_left _ _)
  have hcaplabel : cap ≤ min s₀ (1 / 8) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨cap, hcap, hcapsource, hcapsp.trans hsp1, ?_⟩
  intro σ hσ v hv hpos av
  have hc : D.Controls 0 M (M + 1) 1 (a σ) := hcoeff σ ⟨hσ.1, hσ.2.trans hcapsp⟩
  obtain ⟨hJ, hJne, hu, hmap, hright, hbuffer, hupper⟩ :=
    hgeometry σ ⟨hσ.1, hσ.2.trans hcapsource⟩
  have hreg : PrimitiveRegularity (a σ) (J σ) W := {
    leftMeasurement := (FixedCutoffs.physical hr 1).contDiff.comp_contDiffOn contDiffOn_fst.fst
    rightMeasurement := (FixedCutoffs.physical hr 1).contDiff.comp_contDiffOn contDiffOn_fst.snd
    angular := ha
    high := hh
    leftNormal := hc.normal.smooth.comp (densityEndpoint_contDiff false).contDiffOn (hend false)
    rightNormal := hc.normal.smooth.comp (densityEndpoint_contDiff true).contDiffOn (hend true)
    leftReduced := fun j ↦ (contDiffOn_pi.mp hc.reduced.smooth j).comp
      (densityEndpoint_contDiff false).contDiffOn (hend false)
    rightReduced := fun j ↦ (contDiffOn_pi.mp hc.reduced.smooth j).comp
      (densityEndpoint_contDiff true).contDiffOn (hend true)
    jacobian := hJ
    jacobian_ne_zero := hJne
    covector_ne_zero := hfreqW }
  obtain ⟨hfoot, hfootRange⟩ := source_footpoint_original_domain_regular T hR hV hY hzero hparam
    hs₀ hsource σ ⟨hσ.1, hσ.2.trans hcaplabel⟩
  have hlabel (side : Bool) : ContDiffOn ℝ ∞ (foot σ ∘ densityEndpoint side) W ∧
      MapsTo (foot σ ∘ densityEndpoint side) W
        (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) :=
    ⟨hfoot.comp (densityEndpoint_contDiff side).contDiffOn (fun p hp ↦ hD (hend side hp)),
      (hfootRange.comp (fun p hp ↦ hD (hend side hp))).mono_right
        (closedBall_subset_closedBall (by linarith only [hL] : L / 16 ≤ L / 8))⟩
  have hav : PrimitiveRegularity av (J σ) W :=
    primitiveRegularity_sqrtFootpoints hreg (foot σ)
      (fun side ↦ (hlabel side).1) (fun side ↦ (hlabel side).2) v hv hpos
  have hmaskA : ∀ p ∈ W, av.measurement p.1.1 ≠ 0 → av.measurement p.1.2 ≠ 0 →
      av.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Zmask := by
    dsimp only [av, a]
    as_aux_lemma => exact hmask
  have hhighEq : av.high = high := by
    dsimp only [av, a]
    as_aux_lemma => rfl
  have hsmooth := (amplitude_smooth_and_derivatives_of_punctured_buffer av (J σ) (u σ)
    (augmentedTransportGradient (normalizedTransportPosition T Q₀ σ)) hΩ hav hu hmap
    (augmentedTransportGradient_inverseCoordinates _ _ hright) hmaskA hbuffer
    (hhighEq.symm ▸ hhighZero) hCupper hℓ hlow hupper hS).1
  obtain ⟨hcomplex, hreflected⟩ := fullAmplitudes_contDiff_of_transportAmplitude
    av (J σ) (u σ) Ω S hsmooth
  refine ⟨hcomplex, hreflected,
    fullReflectedMatrixAmplitude_supportedInCenteredBox av (J σ) (u σ) Ω S (4 * r) ?_⟩
  intro x hx j
  exact (PiLp.norm_apply_le x j).trans
    (mem_closedBall_zero_iff.mp (FixedCutoffs.physical_tsupport_four hr 1 (subset_tsupport _ hx)))

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
