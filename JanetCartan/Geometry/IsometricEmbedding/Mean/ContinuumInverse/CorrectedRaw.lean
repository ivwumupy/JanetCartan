module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalizedFamily.SourceRawAdjoint
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.CorrectedScalarProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedChartFamily.SourceFamily

/-!
# Corrected raw adjoints on the retained normalized source

Apply the actual source conic and phase constructors, the original component
profiles, and the corrected initial-scalar reserve to the uniform raw endpoint.
The finite-low density class is `2*(n+1)+14`; every higher norm stays attached
to the low datum norm. Constants and supports precede the source scale and
density. The original seed chart constructs the current lift, and its literal
kernel identifies the result with the same corrected normalized carrier.

Consumer: `PositiveBackground.CorrectedSourceInverse.hwide`, followed by the
same-row inverse and density estimates of `app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumInverse
open ContinuumAdjoint.Canonical ContinuumAdjoint.Canonical.NormalizedFamily
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CarrierSobolev
open ContinuumAdjoint.DensityMultiplier
open ContinuumNormal.CarrierVariation.FamilyInputs PositiveReference
open ContinuumNormal.FrozenModel
open NullTransport ActualFlow FlowAmplitude
open ContinuumAdjoint.DerivativeKernels ModifiedNormalSymbol PhaseExtension AmplitudeProfiles NormalInputs
open Pseudodifferential AmplitudeBound ContinuumRow.TransportKernel

/-- Unit flow factor for `app:ch_background:eq:bg-T`. -/
private theorem unit_scalar_jet_le_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : E) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun _ : E ↦ (1 : ℂ)) p‖ ≤ 1 := by
  cases i with
  | zero => simp
  | succ i => simp [iteratedFDeriv_succ_const]

/-- Construct the literal corrected adjoint, full raw regularity, and both
initial-density estimates on every prescribed submask. The same seed produces
the current chart; no raw estimate, conic inverse or phase profile is assumed.
All constants precede the original finite-low density and source scale, and
the high density norm appears once, at shift `2*(n+1)+14` for raw data and
`2*(n+1)+15` for density. The actual positive-source representative is admissible
by `PositiveBackground.exists_retained_incidence_positive_source_density`
(`app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-density-adjoint`,
`app:ch_background:prop:bg-positive`). -/
theorem exists_corrected_seed_rawAdjoint_for_submasks {n : ℕ} (H : FlatReference n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (hUH : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρ Rc M τ : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρ ⊆ Ω)
    (hpatchStrong : Ω ⊆ (U ∩ ball 0 T.physicalRadius) ×ˢ
      parameterInterior (3 * P.radius / 2))
    (hM : 0 ≤ M) (hτeq : τ = existenceTime Rc (liftedLowBound T M) / 4)
    (hΩscale : ∀ σ ∈ Ioc (0 : ℝ) 1,
      MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (σ • w.1, w.2)) Ω Ω)
    (hRc : 0 < Rc) (hτ : 0 < τ) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρ))
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (c₀ : FlowConstruction.Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc M τ row col H.map)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU c₀.Q.1 c₀.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    {R : ℝ} {V : Set CarrierParameter} (hR : 0 < R)
    (hRphysical : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hV : IsOpen V) (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (FlowConstruction.outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ))
    {L Mc : ℝ} (hL : 0 < L) (hMc : 0 < Mc)
    (hforward : cNorm (Icc (-τ) τ ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8)) 1 c₀.forward ≤ Mc)
    (hRtime : R ≤ L / (64 * Mc))
    (hlabel : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityCoordinates T p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    (hzV : (z₀ 0, spectatorCenter z₀) ∈ V)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {cap : ℝ} (hcap : 0 < cap) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ aMax bMax : ℝ, 0 < aMax ∧ 0 < bMax ∧ aMax < cap ∧
    ∃ χinitial : ContDiffBump (0 : CarrierVariable n),
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧
    ∀ a b : ℝ, ∀ ha : 0 < a, ∀ hb : 0 < b, a ≤ aMax → b ≤ bMax →
    ∃ hcell : 4 * a < 1 / 2,
      supportedChart (n := n) z₀ a ⊆ ball (0 : Euclidean n) R ×ˢ V ∧
    ∃ Cbound Lbound : ℕ → ℝ, (∀ s, 0 ≤ Cbound s) ∧ (∀ s, 0 ≤ Lbound s) ∧
      ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      ∀ v : CarrierVariable n → ℝ, ContDiff ℝ ∞ v →
      (∀ q, 1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8))
        (2 * (n + 1) + 14) (PositiveBackground.densityOnInitialLabels v) ≤ 1 →
      let profile := fun s ↦ 1 + cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8))
        (s + 2 * (n + 1) + 14) (PositiveBackground.densityOnInitialLabels v)
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        (p.2, normalizedTransportPosition T c₀.Q σ p))
        (supportedChart z₀ a) (interior {q | χinitial q = 1}) ∧
      let d := CorrectedPositiveInverse.correctedCarrierData
        (normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse
          (fun _ ↦ 1) ha hcell (angularMask z₀ (NormedSpace.normalize ηb) ha hb)
          FixedCutoffs.highFrequency σ) v
      ∃ A : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ w, A.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) ∧
        (∀ B : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) → B = A) ∧
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
          MemRawSobolev s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ∧
          rawSobolevNorm s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            Cbound s * (‖w‖ + profile s * ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∃ hraw : ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          MemRawSobolev s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)),
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          rawSobolevNorm s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            (2 * Cbound s) * (‖w‖ + profile s * ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) (s + 1),
          let f := (carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 (s + 1) w)
          let hf := (hraw (s + 1) w).mono (by omega : 1 ≤ s + 1)
          MemPhysicalSobolev s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha hb f hf)) ∧
          MemPhysicalSobolev s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha hb χinitial f hf)) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha hb f hf)) ≤
              Lbound s * (‖w‖ + profile (s + 1) * ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha hb χinitial f hf)) ≤
              Lbound s * (‖w‖ + profile (s + 1) * ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) := by
  classical
  have hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius) := by
    intro p hp
    exact ⟨(hpatchStrong hp).1.2,
      fun j ↦ ((hpatchStrong hp).2 j).le.trans (by linarith only [hP.1])⟩
  obtain ⟨sC, hsC, _hsC1, charts, hcharts⟩ :=
    ContinuumRow.NormalizedChartFamily.exists_finite_source_charts_with_lifts
      (ι := Unit) H hUH hbounded (fun _ ↦ T) (fun _ ↦ Ω) (fun _ ↦ hΩ)
      (fun _ ↦ zCell) (fun _ ↦ ρ) (fun _ ↦ Rc) (fun _ ↦ M) (fun _ ↦ τ)
      (fun _ ↦ 1) (fun _ ↦ row) (fun _ ↦ col) (fun _ ↦ hRc) (fun _ ↦ hM)
      (fun _ ↦ zero_lt_one) (fun _ ↦ hτeq) (fun _ ↦ hKΩ) (fun _ ↦ hpatch)
      (fun _ p hp ↦ (hpatchStrong hp).1.1) (fun _ ↦ hΩscale)
      (fun _ ↦ hphysical) (fun _ ↦ hbuffer) (fun _ ↦ c₀) (fun _ ↦ htrans)
  obtain ⟨Ascalar, hAscalar, hscalarProfile⟩ :=
    NormalizedBackground.exists_corrected_initial_scalar_reserve_profiles (n := n) zCell hL
  let E := ball (0 : Euclidean n) R ×ˢ V
  have hE : IsOpen E := isOpen_ball.prod hV
  have hcenter : chartCenter (n := n) z₀ ∈ E := ⟨mem_ball_self hR, hzV⟩
  obtain ⟨ε, hε, hεE⟩ := Metric.isOpen_iff.mp hE (chartCenter z₀) hcenter
  let u := ε / 2
  have hu : 0 < u := half_pos hε
  have hchart : closedBall (chartCenter z₀) u ⊆ E :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεE
  obtain ⟨r, hr, aOuter, haOuter, hacap, har, haR, hphysicalOuter, hcellOuter,
    houter, hcarrier, sG, hsG, hsG1, _hQG, hnormal⟩ :=
    exists_source_normalChart_geometry T H hP hbounded hphysical hz₀ hk hinc hd E hE hcenter
      (lt_min hcap (half_pos hu))
  obtain ⟨aPhase, χPhase, haPhase, haPhaseR, haPhaseOuter, hphysicalPhase,
    _hχ, _hχrange, _hχcompact, _hχsupport, _hχone,
    sP, hsP, _hsP1, B₀, D₀, hB₀, hD₀, _hQP, hphase⟩ :=
    exists_source_supported_phase_inputs T H hP hbounded hphysical z₀ hr haOuter hcarrier
  obtain ⟨sI, hsI, _hsI1, χinitial, hinitial⟩ :=
    exists_source_initialCutoff T H hP hbounded hphysical haPhase haPhaseR
      hphysicalPhase hcarrier
  obtain ⟨rMask, hrMask, hrr, aMax, haMax, haMaxOuter, haMaxPhase, _haMaxR,
    Bnormal, _hBnormal, cJ, hcJ, bInv, _hbInv, VInv, LInv, hVInv, _hVcInv,
    _hLcInv, hLVInv, hnormal⟩ := hnormal aPhase haPhase
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  have hn : 0 < n := by
    by_contra hn
    have hn₀ : n = 0 := by omega
    subst n
    exact hk (Subsingleton.elim _ _)
  let bMax := angularWidth ηb rMask
  have hbMax : 0 < bMax := (angularWidth_spec hηb hrMask).1
  have hauMax : 12 * aMax ≤ u := by
    have hh := hacap.trans_le (min_le_right cap (u / 2))
    linarith
  let σ₀ := min sG (min sP (min sI sC))
  have hcapG {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) : σ ∈ Ioc (0 : ℝ) sG :=
    ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hcapP {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) : σ ∈ Ioc (0 : ℝ) sP :=
    ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hcapI {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) : σ ∈ Ioc (0 : ℝ) sI :=
    ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hcapC {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) : σ ∈ Ioc (0 : ℝ) sC :=
    ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  have hσ₁ : σ₀ ≤ 1 := (min_le_left _ _).trans hsG1
  refine ⟨aMax, bMax, haMax, hbMax,
    by linarith [hacap.trans_le (min_le_left cap (u / 2))],
    χinitial, σ₀, lt_min hsG (lt_min hsP (lt_min hsI hsC)), hσ₁, ?_⟩
  intro aMask b haMask hb haSub hbSub
  have haa : aMask < aOuter := haSub.trans_lt haMaxOuter
  have haMaskPhase : aMask < aPhase := haSub.trans_lt haMaxPhase
  have hcellMask : 4 * aMask < 1 / 2 := by linarith
  have hau : 12 * aMask ≤ u := by linarith
  have hMaskE : supportedChart (n := n) z₀ aMask ⊆ E := by
    intro p hp
    apply hchart
    change dist p (chartCenter z₀) ≤ u
    rw [chartCenter, Prod.dist_eq, max_le_iff, Prod.dist_eq, max_le_iff]
    exact ⟨(mem_closedBall.mp hp.1).trans (by linarith),
      (mem_closedBall.mp hp.2.1).trans (by linarith),
      (mem_closedBall.mp hp.2.2).trans (by linarith)⟩
  obtain ⟨C₀, hC₀, hcomponent⟩ := exists_retained_source_component_profiles H hP T hUH hΩ
    hKΩ hpatch hRc hτ hτR hbuffer hphysical c₀ htrans hR hRphysical hRU hV hVP hflow
    z₀ hu haMask hau hchart hcellMask
    (angularMask z₀ (NormedSpace.normalize ηb) haMask hb) FixedCutoffs.highFrequency
  obtain ⟨W, hW, hw⟩ := exists_fixed_halfOrderRadialFactor_jet_bounds (n := n)
  obtain ⟨P₀, N₀, hP₀, hN₀, hpn⟩ := exists_fixed_angular_reserve_profiles z₀
    (NormedSpace.normalize ηb) haMask hb
  have hboxMask : closedBall (0 : Euclidean n) (4 * aMask) ⊆
      DifferentialChart.chartBox (4 * aMask) := by
    intro x hx j
    exact (PiLp.norm_apply_le x j).trans (mem_closedBall_zero_iff.mp hx)
  choose Cbound hCbound hbound using fun s ↦
    UniformEndpoint.exists_uniform_scalarTransportCarrierAdjoint_periodic_raw_bound
      (N := embeddingDimension n) (FixedCutoffs.physical haMask 1)
      (FixedCutoffs.closedBall_four_subset_cell hcellMask) hcellMask hboxMask
      (fun x hx ↦ FixedCutoffs.physical_eq_zero_outside_four haMask 1 hx)
      1 Bnormal (cJ / ‖ηb‖) (normalSupport T z₀ ηb rMask aMax)
      (closedBall (0 : Euclidean n) (4 * aMax)) (carrierSupport z₀ (r := aMax))
      (closedDirections ηb rMask) (isCompact_closedBall _ _) (carrierSupport_compact z₀)
      (closedDirections_compact ηb rMask) hn (normalSupport_directions_unit ηb rMask)
      W P₀ N₀ (Ascalar s) B₀ (fun _ ↦ 1) C₀ D₀
      hW hC₀ hP₀ hN₀ (hAscalar s) hB₀ (fun _ ↦ zero_le_one) hD₀ s
  choose L hLdensity hdensity using fun s ↦
    exists_density_bounds z₀ (NormedSpace.normalize ηb) haMask hb χinitial s
  refine ⟨hcellMask, hMaskE, Cbound, (fun s ↦ L s * (2 * Cbound (s + 1))), hCbound,
    (fun s ↦ mul_nonneg (hLdensity s) (mul_nonneg (by norm_num) (hCbound (s + 1)))), ?_⟩
  intro σ hσ v hv hinterval hlow profile
  let current := charts σ (hcapC hσ) ()
  obtain ⟨_Ψ, _hΨ, _hf, _hy, _hi, hrankσ, _rest⟩ := hcharts σ (hcapC hσ) ()
  let Q := current.Q
  have hQ : Q.1 = ProjectedStressFrame.projectedStress (sourceDilation H.map σ) :=
    current.frame_eq
  have hrank : HasFullNormalRankOn H.map U := fun x hx ↦ H.fullNormalRank x (hUH hx)
  have hposition : EqOn (transportPosition T Q) (normalizedTransportPosition T c₀.Q σ) E := by
    apply (SourceMatching.current_transportPosition_source_dilation_on_patch T c₀.Q Q H.contDiff hrank
        hphysical c₀.frame_eq htrans hσ.1 (hσ.2.trans hσ₁) hQ).1.mono
    intro p hp
    exact ⟨ball_subset_ball hRphysical hp.1,
      fun j ↦ (hVP hp.2 j).trans (by linarith [hP.1])⟩
  refine ⟨?_, ?_⟩
  · intro p hp
    change (p.2, normalizedTransportPosition T c₀.Q σ p) ∈ interior {q | χinitial q = 1}
    rw [← hposition (hMaskE hp)]
    exact hinitial σ (hcapI hσ) Q hQ (supportedChart_mono z₀ haMaskPhase.le hp)
  let unit := normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse
    (fun _ ↦ 1) haMask hcellMask (angularMask z₀ (NormedSpace.normalize ηb) haMask hb)
    FixedCutoffs.highFrequency σ
  let corrected := CorrectedPositiveInverse.correctedCarrierData unit v
  let d₀ := data T current.Q (sourceDilation H.map σ) row col current.forward current.inverse
    (fun _ ↦ σ) haMask hcellMask (angularMask z₀ (NormedSpace.normalize ηb) haMask hb)
    FixedCutoffs.highFrequency
  obtain ⟨hf, hInv, htransverse, hg, _hJdomain, hclosed, himage⟩ :=
    hnormal σ (hcapG hσ) Q hQ
  obtain ⟨_hYext, _hcompact, hagree, _hgap, hΦext, hgraphExt, hInitialField, hVfield,
    hphaseL, hphaseV, hgraphProfile, hfieldProfile⟩ := hphase σ (hcapP hσ) Q hQ
  let Yext := affineExtension (frozenSpatialReference T (z₀ 0, spectatorCenter z₀))
    χPhase (transportPosition T Q)
  have hagreePhase : EqOn Yext (transportPosition T Q) (supportedChart z₀ aPhase) :=
    fun p hp ↦ (hagree p hp).eq_of_nhds
  have hagreeMask := hagreePhase.mono (supportedChart_mono z₀ haMaskPhase.le)
  let ν := fun p : AdjointJetPoint n ↦
    chartBump z₀ haMask (p.2, p.1) • d₀.normalField p.2 p.1
  let scalar := extendedInitialScalar zCell hL
    (fun q ↦ positiveDensityAmplitude 1 (PositiveBackground.densityOnInitialLabels v q))
  obtain ⟨_hscalar, hscalarComplex, _hscalarCompact, hscalarJets⟩ :=
    hscalarProfile v hv hinterval hlow
  have hprofile (s : ℕ) : 1 ≤ profile s :=
    le_add_of_nonneg_right (cNorm_nonneg _ _ _)
  let d := scalarTransportData d₀ Yext scalar (fun _ ↦ 1) ν
  obtain ⟨_hνglobal, hcglobal, hcprofile⟩ := hcomponent σ ⟨hσ.1, hσ.2.trans hσ₁⟩ current
  have hm : ContDiff ℝ ∞ (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)) :=
    angularMask_complex_contDiff z₀ (NormedSpace.normalize ηb) haMask hb
  have hcg j : ContDiff ℝ ∞ (carrierChartGeometryComponent d (FixedCutoffs.physical haMask 1) ν j) :=
    hcglobal j
  have hsmooth j : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦
      frequencyScaleAmplitude (halfOrderRadialFactor d.highCutoff)
        (carrierChartNormalizedComponent d (FixedCutoffs.physical haMask 1) j) p.1 p.2.1 p.2.2) :=
    frequencyScale_carrierChartNormalizedComponent_contDiff d (FixedCutoffs.physical haMask 1)
      ν scalar (fun _ ↦ 1)
      (fun z x ↦ scalarTransportData_normalField d₀ Yext _ _ ν x z) rfl j (hcg j) hm
      hscalarComplex contDiff_const hgraphExt
  have hsupp (j : Fin n) (z : CarrierParameter) (x : Euclidean n) (η : Euclidean (n - 1))
      (hne : frequencyScaleAmplitude (halfOrderRadialFactor d.highCutoff)
        (carrierChartNormalizedComponent d (FixedCutoffs.physical haMask 1) j) z x η ≠ 0) :
      z ∈ carrierSupport z₀ (r := aMax) ∧ x ∈ closedBall 0 (4 * aMax) ∧
        ‖η‖⁻¹ • η ∈ closedDirections ηb rMask ∧ 1 ≤ ‖η‖ := by
    obtain ⟨hz, hx, hθ, hrad⟩ := frequencyScale_carrierChartNormalizedComponent_support d z₀
      (NormedSpace.normalize ηb) haMask hb rfl rfl j z x η hne
    have hhalf : aMask / 2 ≤ aMax / 2 := by linarith
    refine ⟨⟨closedBall_subset_closedBall hhalf hz.1, closedBall_subset_closedBall hhalf hz.2⟩,
      closedBall_subset_closedBall (by linarith : 4 * aMask ≤ 4 * aMax) hx, ?_, hrad⟩
    change ‖η‖⁻¹ • η ∈ sphere 0 1 ∩ closedBall (NormedSpace.normalize ηb) (bMax / 2)
    exact ⟨hθ.1, closedBall_subset_closedBall (by linarith : b / 2 ≤ bMax / 2) hθ.2⟩
  have har₀ : aOuter ≤ r := by linarith
  have horder (s : ℕ) : ∃ A : ComplexOutputL2 n →L[ℂ] CarrierL2 n,
      (∀ w, A w =ᵐ[carrierMeasure n] carrierAdjointIntegral corrected w) ∧
      ∀ w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
        MemRawSobolev s (A (PeriodicSobolevSpace.toL2 s w)) ∧
        rawSobolevNorm s (A (PeriodicSobolevSpace.toL2 s w)) ≤
          Cbound s * (‖w‖ + profile s * ‖PeriodicSobolevSpace.toL2 s w‖) := by
    have hbound' := hbound s d rfl (fun _ _ ↦ rfl)
      (fun x _ ↦ FixedCutoffs.periodic_apply haMask hcellMask 1 x)
      ν scalar (fun _ ↦ 1)
      (fun z x ↦ scalarTransportData_normalField d₀ Yext _ _ ν x z)
      hcg hm hscalarComplex contDiff_const hgraphExt hΦext
      _ _ hg (fun j ↦ normalChart_primitiveRegularity T Q hηb hr hf hInv htransverse
        hVInv hLVInv hcJ _ (hsmooth j)) hsupp
      (initialField Yext) (carrierField Yext) hInitialField hVfield
      (normalChart_measurePreserving T Q z₀ ηb r (6 * aOuter) aPhase)
      (normalChart_coordinates_symm_continuous T Q z₀ ηb r (6 * aOuter) aPhase)
      (normalChart_domain_of_conicBuffers T Q hηb hr haOuter har₀ hrr.le haMaxOuter.le haMaxPhase)
      (normalChart_push_contDiffOn T Q hηb hr hf).continuousOn
      (fun x y v ↦ (normalChart_domain_open T Q z₀ ηb r (6 * aOuter) aPhase x y v).measurableSet)
      (fun x y v w hw ↦ (normalChart_hasFDerivAt T Q hηb hr hf x y v hw).hasFDerivWithinAt)
      (normalChart_forward_injective T Q hηb hr hInv htransverse)
      (fun x y v w hw ↦ normalChart_inverse_forward T Q hηb hr hInv htransverse x y v hw)
      (normalChart_phase_identity T Q hP hr haR (by linarith) hcarrier Yext hagreePhase)
      (fun p _ hx hy ↦ normalSupport_of_conicBuffers T Q p hx hy) hclosed himage
      (fun z x η h _ ↦ hphaseL z x η h) (fun z x η h _ ↦ hphaseV z x η h)
    obtain ⟨hUopen, hunit, hangular⟩ := adjointAngularGraph_neighborhood (n := n)
    obtain ⟨A, hrep, hraw⟩ := hbound' (profile s) (hprofile s) {0}ᶜ hUopen hunit hangular
      (fun R' _ p _ ↦ (scaled_halfOrderRadialFactor_contDiff R').contDiffAt)
      (fun R' hR' p hp i _ ↦ hw R' hR' p hp i)
      (fun j p i _ ↦ by
        change ‖iteratedFDeriv ℝ i (carrierChartGeometryComponent d₀
          (FixedCutoffs.physical haMask 1) ν j) p‖ ≤ _
        exact (hcprofile j p i).trans (le_mul_of_one_le_right (hC₀ j i)
          (Real.one_le_rpow (hprofile s) (by positivity))))
      (fun R' hR' p hp i _ ↦ (hpn (profile s) (hprofile s) s R' hR' p hp).1 i)
      (fun R' hR' p hp i hi _ ↦ (hpn (profile s) (hprofile s) s R' hR' p hp).2 i hi)
      (fun p i hi ↦ hscalarJets s (profile s) le_rfl
        (p.1, d.transportedPosition p.2 p.1) i hi)
      (fun p i hi _ ↦ by
        exact (hgraphProfile p i hi).trans (le_mul_of_one_le_right (hB₀ i)
          (Real.one_le_rpow (hprofile s) (by positivity))))
      (fun p i _ ↦ by
        simpa only [one_mul, Complex.ofReal_one] using
          (unit_scalar_jet_le_one p i).trans
            (Real.one_le_rpow (hprofile s) (by positivity)))
      (fun ds _ p _ e he j i _ ↦ by
        exact (hfieldProfile ds p e he j i).trans (le_mul_of_one_le_right (hD₀ ds i)
          (Real.one_le_rpow (hprofile s) (by positivity))))
    have hkernel : carrierKernel d = carrierKernel corrected := by
      exact (NormalizedBackground.retained_source_corrected_scalarTransportData_kernel_and_integrals
        T hP hΩ hKΩ hpatchStrong hRc hτ hτR hbuffer H.contDiff hrank hphysical c₀ htrans
        (fun x _ ↦ H.inducedMetric_eq_one x) hL hMc hforward hRtime V hflow hlabel
        hσ.1 (hσ.2.trans hσ₁) current hrankσ haMask hcellMask z₀ (NormedSpace.normalize ηb)
        haMask hb le_rfl FixedCutoffs.highFrequency hMaskE Yext hagreeMask v
        (fun p ↦ le_trans (by norm_num) (hinterval p).1)).1
    refine ⟨A, ?_, ?_⟩
    · intro w
      exact (hrep w).trans (Filter.Eventually.of_forall fun u ↦
        congrFun (congrFun (carrierAdjointIntegral_congr_kernel hkernel) w) u)
    · simpa only [one_mul] using hraw
  obtain ⟨A₀, hA₀, _⟩ := horder 0
  let A := A₀.adjoint
  have hA : A.adjoint = A₀ := ContinuousLinearMap.adjoint_adjoint A₀
  have hrep w : A.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral corrected w := by
    rw [hA]
    exact hA₀ w
  have hraw (s : ℕ) (w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s) :
      MemRawSobolev s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ∧
      rawSobolevNorm s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
        Cbound s * (‖w‖ + profile s * ‖PeriodicSobolevSpace.toL2 s w‖) := by
    obtain ⟨Aₛ, hAₛ, hbnd⟩ := horder s
    have he := literalCarrierAdjointOperator_unique corrected Aₛ A₀ hAₛ hA₀
    simpa only [hA, he] using hbnd w
  have hreal (s : ℕ) (w : PeriodicSobolevSpace n (Euclidean n) s) :=
    carrierChannel_adjoint_raw_bound corrected A A.adjoint hrep hrep (hCbound s)
      (zero_le_one.trans (hprofile s)) (hraw s) w
  refine ⟨A, hrep, ?_, hraw, (fun s w ↦ (hreal s w).1),
    (fun s w ↦ (hreal s w).2), ?_⟩
  · intro B hB
    have he := literalCarrierAdjointOperator_unique corrected B.adjoint A₀ hB hA₀
    simpa only [ContinuousLinearMap.adjoint_adjoint] using congrArg ContinuousLinearMap.adjoint he
  · intro s w
    obtain ⟨_, huncut, hcut⟩ := hdensity s _ (hreal (s + 1) w).1
    refine ⟨huncut.1, hcut.1, ?_, ?_⟩
    · exact (huncut.2.trans
        (mul_le_mul_of_nonneg_left (hreal (s + 1) w).2 (hLdensity s))).trans_eq
          (mul_assoc _ _ _).symm
    · exact (hcut.2.trans
        (mul_le_mul_of_nonneg_left (hreal (s + 1) w).2 (hLdensity s))).trans_eq
          (mul_assoc _ _ _).symm

end JanetCartan.ContinuumInverse
