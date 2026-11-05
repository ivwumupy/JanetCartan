module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalizedFamily.SourceConic
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalizedFamily.SourceComponents
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalizedFamily.SourceInitialCutoff
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.LocalAdjoint
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RealAdjoint
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.Density
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.KernelMatching

/-!
# The literal raw adjoint of a supplied normalized source chart

Instantiate the uniform scalar endpoint with the actual source phase, conic
inverse and full amplitude profiles. All constants and cutoffs precede the
source scale. Uniqueness of the literal integral representative retains one
operator at every Sobolev order. No raw regularity or operator bound is assumed.
Realification keeps both quadratures. The same fixed initial-space cutoff and
half-order density multiplier give the full initial-variable estimates before
and after the cutoff, with constants still preceding the source scale.

Consumers: the normalized finite row and `PositiveBackground.SourceInverse`
(`app:ch_background:prop:bg-adjoint`, `app:ch_background:prop:bg-normalized`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CarrierSobolev DensityMultiplier
open ContinuumNormal.CarrierVariation.FamilyInputs PositiveReference
open ContinuumNormal.FrozenModel
open NullTransport ActualFlow FlowAmplitude
open DerivativeKernels ModifiedNormalSymbol PhaseExtension AmplitudeProfiles NormalInputs
open Pseudodifferential AmplitudeBound ContinuumRow.TransportKernel

/-- Unit scalar and flow factors have unit jet budget. The full original
normal carries the source scalar (`app:ch_background:eq:bg-T`). -/
private theorem unit_scalar_jet_le_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : E) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun _ : E ↦ (1 : ℂ)) p‖ ≤ 1 := by
  cases i with
  | zero => simp
  | succ i => simp [iteratedFDeriv_succ_const]

/-- Every prescribed submask of one fixed conic support has an actual literal
raw adjoint and both density estimates. The support caps, initial cutoff and
source interval precede the prescribed physical and angular masks; all-order
constants then precede `σ`. The conic inverse and its Jacobian are retained
on the original larger support, while the actual kernel uses exactly the
supplied submask. No regularity or operator estimate is assumed.

This allows normalized selection to choose its final incidence masks inside
the adjoint-compatible support without identifying independent mask choices.
The supplied seed chart retains its original minor and ODE cylinder. No
contracted null-flow chart is needed for the normalized kernel construction
(`app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-density-adjoint`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_normalized_seed_rawAdjoint_for_submasks {n : ℕ} (H : FlatReference n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (hUH : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρ Rc M τ : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρ ⊆ Ω)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius))
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
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        (p.2, normalizedTransportPosition T c₀.Q σ p))
        (supportedChart z₀ a) (interior {q | χinitial q = 1}) ∧
      let d := normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse
        (fun _ ↦ 1) ha hcell (angularMask z₀ (NormedSpace.normalize ηb) ha hb)
        FixedCutoffs.highFrequency σ
      (∀ cσ : FlowConstruction.Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
        ((0 : Euclidean (n - 1)), zCell) Rc M τ row col (sourceDilation H.map σ),
        carrierKernel (data T cσ.Q (sourceDilation H.map σ) row col cσ.forward cσ.inverse
          (fun _ ↦ σ) ha hcell (angularMask z₀ (NormedSpace.normalize ηb) ha hb)
          FixedCutoffs.highFrequency) = carrierKernel d) ∧
      ∃ A : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ w, A.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) ∧
        (∀ B : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) → B = A) ∧
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
          MemRawSobolev s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ∧
          rawSobolevNorm s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            Cbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∃ hraw : ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          MemRawSobolev s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)),
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          rawSobolevNorm s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            (2 * Cbound s) * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) (s + 1),
          let f := (carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 (s + 1) w)
          let hf := (hraw (s + 1) w).mono (by omega : 1 ≤ s + 1)
          MemPhysicalSobolev s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha hb f hf)) ∧
          MemPhysicalSobolev s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha hb χinitial f hf)) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha hb f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha hb χinitial f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) := by
  classical
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
    sP, hsP, _hsP1, B₀, D₀, hB₀, hD₀, hQP, hphase⟩ :=
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
  let σ₀ := min sG (min sP sI)
  have hcapG {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) : σ ∈ Ioc (0 : ℝ) sG :=
    ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hcapP {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) : σ ∈ Ioc (0 : ℝ) sP :=
    ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hcapI {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) : σ ∈ Ioc (0 : ℝ) sI :=
    ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hσ₁ : σ₀ ≤ 1 := (min_le_left _ _).trans hsG1
  refine ⟨aMax, bMax, haMax, hbMax,
    by linarith [hacap.trans_le (min_le_left cap (u / 2))],
    χinitial, σ₀, lt_min hsG (lt_min hsP hsI), hσ₁, ?_⟩
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
  obtain ⟨C₀, hC₀, hcomponent⟩ := exists_normalized_source_component_profiles H hP T hUH hΩ
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
      W P₀ N₀ (fun _ ↦ 1) B₀ (fun _ ↦ 1) C₀ D₀
      hW hC₀ hP₀ hN₀ (fun _ ↦ zero_le_one) hB₀ (fun _ ↦ zero_le_one) hD₀ s
  choose L hLdensity hdensity using fun s ↦
    exists_density_bounds z₀ (NormedSpace.normalize ηb) haMask hb χinitial s
  refine ⟨hcellMask, hMaskE, Cbound, (fun s ↦ L s * (2 * Cbound (s + 1))), hCbound,
    (fun s ↦ mul_nonneg (hLdensity s) (mul_nonneg (by norm_num) (hCbound (s + 1)))), ?_⟩
  intro σ hσ
  obtain ⟨Q, hQ⟩ := hQP σ (hcapP hσ)
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
  let d₀ := normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse
    (fun _ ↦ 1) haMask hcellMask (angularMask z₀ (NormedSpace.normalize ηb) haMask hb)
    FixedCutoffs.highFrequency σ
  constructor
  · intro cσ
    let dcurrent := data T cσ.Q (sourceDilation H.map σ) row col cσ.forward cσ.inverse
      (fun _ ↦ σ) haMask hcellMask (angularMask z₀ (NormedSpace.normalize ηb) haMask hb)
      FixedCutoffs.highFrequency
    obtain ⟨_, _, hscalar, _, _⟩ :=
      ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.retained_charts_source_dilation
        T hΩ hKΩ hpatch hRc hτ hτR hbuffer H.contDiff hrank hphysical c₀ htrans
        (fun x _ ↦ H.inducedMetric_eq_one x) hσ.1 (hσ.2.trans hσ₁) cσ
    change carrierKernel dcurrent = carrierKernel d₀

    apply NormalizedSelection.carrierKernel_eq_normalized_of_scalar_transport
      T c₀.Q cσ.Q H.contDiff hrank hphysical c₀.frame_eq htrans
      hσ.1 (hσ.2.trans hσ₁) cσ.frame_eq row col c₀.forward c₀.inverse cσ.forward cσ.inverse
      (fun _ ↦ 1) (fun _ ↦ σ) hP haMask hcellMask
      (angularMask z₀ (NormedSpace.normalize ηb) haMask hb) FixedCutoffs.highFrequency
      (W := ball (0 : Euclidean n) R ×ˢ (parameter '' V))
    · rintro ⟨x, z⟩ ⟨hx, q, hq, rfl⟩
      exact ⟨ball_subset_ball hRphysical hx, fun j ↦ (hVP hq j).trans (by linarith [hP.1])⟩
    · intro x z η hx hz
      obtain ⟨hza, hzv, _⟩ := angularMask_nonzero z₀ (NormedSpace.normalize ηb) haMask hb hz
      have hxm : AmplitudeBound.centeredTorusRepresentative x ∈ closedBall (0 : Euclidean n) (4 * aMask) :=
        FixedCutoffs.physical_tsupport_four haMask 1 (subset_tsupport _ hx)
      have hpm : (AmplitudeBound.centeredTorusRepresentative x, z) ∈
          supportedChart (n := n) z₀ aMask :=
        ⟨hxm, ball_subset_closedBall hza, ball_subset_closedBall hzv⟩
      have hp : (AmplitudeBound.centeredTorusRepresentative x, z) ∈ E := hMaskE hpm
      exact ⟨hp.1, z, hp.2, rfl⟩
    · rintro ⟨x, z⟩ ⟨hx, q, hq, rfl⟩
      exact hscalar (cσ.small_subset ((FlowConstruction.outputCylinder_spec hRc hτ).2
        (hflow (x := (x, q)) ⟨hx, hq⟩)))
  obtain ⟨hf, hInv, htransverse, hg, _hJdomain, hclosed, himage⟩ :=
    hnormal σ (hcapG hσ) Q hQ
  obtain ⟨_hYext, _hcompact, hagree, _hgap, hΦext, hgraphExt, hL, hVfield,
    hphaseL, hphaseV, hgraphProfile, hfieldProfile⟩ := hphase σ (hcapP hσ) Q hQ
  let Yext := affineExtension (frozenSpatialReference T (z₀ 0, spectatorCenter z₀))
    χPhase (transportPosition T Q)
  have hagreePhase : EqOn Yext (transportPosition T Q) (supportedChart z₀ aPhase) :=
    fun p hp ↦ (hagree p hp).eq_of_nhds
  have hagreeMask := hagreePhase.mono (supportedChart_mono z₀ haMaskPhase.le)
  let ν := fun p : AdjointJetPoint n ↦
    chartBump z₀ haMask (p.2, p.1) • d₀.normalField p.2 p.1
  let d := scalarTransportData d₀ Yext (fun _ ↦ 1) (fun _ ↦ 1) ν
  obtain ⟨_hνglobal, hcglobal, hcprofile⟩ := hcomponent σ ⟨hσ.1.le, hσ.2.trans hσ₁⟩
  have hm : ContDiff ℝ ∞ (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)) :=
    angularMask_complex_contDiff z₀ (NormedSpace.normalize ηb) haMask hb
  have hcg j : ContDiff ℝ ∞ (carrierChartGeometryComponent d (FixedCutoffs.physical haMask 1) ν j) :=
    hcglobal j
  have hsmooth j : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦
      frequencyScaleAmplitude (halfOrderRadialFactor d.highCutoff)
        (carrierChartNormalizedComponent d (FixedCutoffs.physical haMask 1) j) p.1 p.2.1 p.2.2) :=
    frequencyScale_carrierChartNormalizedComponent_contDiff d (FixedCutoffs.physical haMask 1)
      ν (fun _ ↦ 1) (fun _ ↦ 1)
      (fun z x ↦ scalarTransportData_normalField d₀ Yext _ _ ν x z) rfl j (hcg j) hm
      contDiff_const contDiff_const hgraphExt
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
      (∀ w, A w =ᵐ[carrierMeasure n] carrierAdjointIntegral d₀ w) ∧
      ∀ w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
        MemRawSobolev s (A (PeriodicSobolevSpace.toL2 s w)) ∧
        rawSobolevNorm s (A (PeriodicSobolevSpace.toL2 s w)) ≤
          Cbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖) := by
    have hbound' := hbound s d rfl (fun _ _ ↦ rfl)
      (fun x _ ↦ FixedCutoffs.periodic_apply haMask hcellMask 1 x)
      ν (fun _ ↦ 1) (fun _ ↦ 1)
      (fun z x ↦ scalarTransportData_normalField d₀ Yext _ _ ν x z)
      hcg hm contDiff_const contDiff_const hgraphExt hΦext
      _ _ hg (fun j ↦ normalChart_primitiveRegularity T Q hηb hr hf hInv htransverse
        hVInv hLVInv hcJ _ (hsmooth j)) hsupp
      (initialField Yext) (carrierField Yext) hL hVfield
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
    obtain ⟨A, hrep, hraw⟩ := hbound' 1 le_rfl {0}ᶜ hUopen hunit hangular
      (fun R' _ p _ ↦ (scaled_halfOrderRadialFactor_contDiff R').contDiffAt)
      (fun R' hR' p hp i _ ↦ hw R' hR' p hp i)
      (fun j p i _ ↦ by
        simpa only [Real.one_rpow, mul_one, d,
          carrierChartGeometryComponent_scalarTransportData] using hcprofile j p i)
      (fun R' hR' p hp i _ ↦ (hpn 1 le_rfl s R' hR' p hp).1 i)
      (fun R' hR' p hp i hi _ ↦ (hpn 1 le_rfl s R' hR' p hp).2 i hi)
      (fun p i _ ↦ by
        simpa only [Real.one_rpow, one_mul, Complex.ofReal_one] using
          unit_scalar_jet_le_one (p.1, d.transportedPosition p.2 p.1) i)
      (fun p i hi _ ↦ by
        simpa only [Real.one_rpow, mul_one, d, scalarTransportData, Yext] using
          hgraphProfile p i hi)
      (fun p i _ ↦ by
        simpa only [Real.one_rpow, one_mul, Complex.ofReal_one] using unit_scalar_jet_le_one p i)
      (fun ds _ p _ e he j i _ ↦ by
        simpa only [Real.one_rpow, mul_one] using hfieldProfile ds p e he j i)
    have hkernel : carrierKernel d = carrierKernel d₀ := by
      apply carrierKernel_scalarTransportData_eq
      intro x _ hx z θ hθ
      obtain ⟨hz, hv, _⟩ := angularMask_nonzero z₀ (NormedSpace.normalize ηb) haMask hb hθ
      have hxm : AmplitudeBound.centeredTorusRepresentative x ∈
          closedBall (0 : Euclidean n) (4 * aMask) :=
        FixedCutoffs.physical_tsupport_four haMask 1 (subset_tsupport _ hx)
      have hp : (AmplitudeBound.centeredTorusRepresentative x, z) ∈
          supportedChart (n := n) z₀ aMask :=
        ⟨hxm, ball_subset_closedBall hz, ball_subset_closedBall hv⟩
      refine ⟨(hagreeMask hp).trans (hposition (hMaskE hp)), ?_⟩
      change (1 * 1 : ℝ) • (chartBump z₀ haMask (AmplitudeBound.centeredTorusRepresentative x, z) •
        d₀.normalField (AmplitudeBound.centeredTorusRepresentative x) z) = _
      have hbump : chartBump z₀ haMask (AmplitudeBound.centeredTorusRepresentative x, z) =
          (1 : ℝ) := (chartBump_eventuallyEq_one z₀ haMask hp).eq_of_nhds
      simp only [hbump, one_mul, one_smul]
      rfl
    refine ⟨A, ?_, ?_⟩
    · intro w
      exact (hrep w).trans (Filter.Eventually.of_forall fun u ↦
        congrFun (congrFun (carrierAdjointIntegral_congr_kernel hkernel) w) u)
    · simpa only [one_mul] using hraw
  obtain ⟨A₀, hA₀, _⟩ := horder 0
  let A := A₀.adjoint
  have hA : A.adjoint = A₀ := ContinuousLinearMap.adjoint_adjoint A₀
  have hrep w : A.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d₀ w := by
    rw [hA]
    exact hA₀ w
  have hraw (s : ℕ) (w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s) :
      MemRawSobolev s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ∧
      rawSobolevNorm s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
        Cbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖) := by
    obtain ⟨Aₛ, hAₛ, hbnd⟩ := horder s
    have he := literalCarrierAdjointOperator_unique d₀ Aₛ A₀ hAₛ hA₀
    simpa only [hA, he] using hbnd w
  have hreal (s : ℕ) (w : PeriodicSobolevSpace n (Euclidean n) s) :=
    carrierChannel_adjoint_raw_bound d₀ A A.adjoint hrep hrep (hCbound s) zero_le_one
      (by simpa only [one_mul] using hraw s) w
  simp only [one_mul] at hreal
  refine ⟨A, hrep, ?_, hraw, (fun s w ↦ (hreal s w).1),
    (fun s w ↦ (hreal s w).2), ?_⟩
  · intro B hB
    have he := literalCarrierAdjointOperator_unique d₀ B.adjoint A₀ hB hA₀
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


/-- Every prescribed submask of one fixed conic support has an actual literal
raw adjoint and both density estimates. The support caps, initial cutoff and
source interval precede the prescribed physical and angular masks; all-order
constants then precede `σ`. The conic inverse and its Jacobian are retained
on the original larger support, while the actual kernel uses exactly the
supplied submask. No regularity or operator estimate is assumed.

This allows normalized selection to choose its final incidence masks inside
the adjoint-compatible support without identifying independent mask choices.
The seed and source charts remain on the same minor and ODE cylinder
(`app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-density-adjoint`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_retained_source_rawAdjoint_for_submasks {n : ℕ} (H : FlatReference n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (hUH : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρ Rc M τ : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρ ⊆ Ω)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius))
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
    ∃ Cbound Lbound : ℕ → ℝ, (∀ s, 0 ≤ Cbound s) ∧ (∀ s, 0 ≤ Lbound s) ∧
      ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      ∀ cσ : FlowConstruction.Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
        ((0 : Euclidean (n - 1)), zCell) Rc M τ row col (sourceDilation H.map σ),
      MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.2, transportPosition T cσ.Q p))
        (supportedChart z₀ a) (interior {q | χinitial q = 1}) ∧
      let d := data T cσ.Q (sourceDilation H.map σ) row col cσ.forward cσ.inverse
        (fun _ ↦ σ) ha hcell (angularMask z₀ (NormedSpace.normalize ηb) ha hb)
        FixedCutoffs.highFrequency
      let e := normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse
        (fun _ ↦ 1) ha hcell (angularMask z₀ (NormedSpace.normalize ηb) ha hb)
        FixedCutoffs.highFrequency σ
      carrierKernel d = carrierKernel e ∧
      ∃ A : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ w, A.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) ∧
        (∀ B : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) → B = A) ∧
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
          MemRawSobolev s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ∧
          rawSobolevNorm s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            Cbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∃ hraw : ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          MemRawSobolev s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)),
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          rawSobolevNorm s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            (2 * Cbound s) * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) (s + 1),
          let f := (carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 (s + 1) w)
          let hf := (hraw (s + 1) w).mono (by omega : 1 ≤ s + 1)
          MemPhysicalSobolev s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha hb f hf)) ∧
          MemPhysicalSobolev s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha hb χinitial f hf)) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha hb f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha hb χinitial f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) := by
  classical
  obtain ⟨aMax, bMax, haMax, hbMax, hacap, χinitial, σ₀, hσ₀, hσ₁, hsubmask⟩ :=
    exists_normalized_seed_rawAdjoint_for_submasks H hP T hUH hbounded hΩ hKΩ hpatch
      hRc hτ hτR hbuffer hphysical c₀ htrans hR hRphysical hRU hV hVP hflow
      hz₀ hzV hk hinc hd hcap
  refine ⟨aMax, bMax, haMax, hbMax, hacap, χinitial, σ₀, hσ₀, hσ₁, ?_⟩
  intro aMask b haMask hb haSub hbSub
  obtain ⟨hcellMask, hMaskE, Cbound, Lbound, hCbound, hLbound, hnormalizedAdjoint⟩ :=
    hsubmask aMask b haMask hb haSub hbSub
  refine ⟨hcellMask, Cbound, Lbound, hCbound, hLbound, ?_⟩
  intro σ hσ cσ
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  let E := ball (0 : Euclidean n) R ×ˢ V
  let d₀ := data T cσ.Q (sourceDilation H.map σ) row col cσ.forward cσ.inverse
    (fun _ ↦ σ) haMask hcellMask (angularMask z₀ (NormedSpace.normalize ηb) haMask hb)
    FixedCutoffs.highFrequency
  let e := normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse
    (fun _ ↦ 1) haMask hcellMask (angularMask z₀ (NormedSpace.normalize ηb) haMask hb)
    FixedCutoffs.highFrequency σ
  have hrank : HasFullNormalRankOn H.map U := fun x hx ↦ H.fullNormalRank x (hUH hx)
  obtain ⟨hplateau, hcurrent, A, hrep, hunique, hcomplex, hreal, hrealBound, hdensity⟩ :=
    hnormalizedAdjoint σ hσ
  have hnormalized : carrierKernel d₀ = carrierKernel e := hcurrent cσ
  refine ⟨?_, hnormalized, A, ?_, ?_, hcomplex, hreal, hrealBound, hdensity⟩
  · intro p hp
    have hposition := (SourceMatching.current_transportPosition_source_dilation_on_patch T c₀.Q cσ.Q H.contDiff hrank
        hphysical c₀.frame_eq htrans hσ.1 (hσ.2.trans hσ₁) cσ.frame_eq).1
    change (p.2, transportPosition T cσ.Q p) ∈ interior {q | χinitial q = 1}
    rw [hposition ⟨ball_subset_ball hRphysical (hMaskE hp).1,
      fun j ↦ (hVP (hMaskE hp).2 j).trans (by linarith [hP.1])⟩]
    exact hplateau hp
  · intro w
    rw [carrierAdjointIntegral_congr_kernel hnormalized]
    exact hrep w
  · intro B hB
    apply hunique B
    intro w
    rw [← carrierAdjointIntegral_congr_kernel hnormalized]
    exact hB w

/-- Construct the actual bounded carrier and its literal all-order raw adjoint
for every supplied source chart of the SAME retained seed. The phase, conic
inverse, full normal and detector budgets are all instantiated from their
normalized producers. The smaller masks and one initial cutoff are fixed
before the scale; the original carrier measure, Fourier normalization and
half-order factor are those of the uniform endpoint.
The same constructed operator supplies the real raw estimate and both
initial-density estimates; their constants also precede the source scale.

The finite-family producer supplies the seed and source charts, including
their original minor, coefficient ball and ODE cylinder. No desired adjoint
estimate is among these inputs. The incidence center may differ from the
ODE center (`app:ch_background:prop:bg-adjoint`, `bg-derivative-trade`,
`bg-density-adjoint`, `bg-normalized`). -/
theorem exists_retained_source_rawAdjoint {n : ℕ} (H : FlatReference n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (hUH : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρ Rc M τ : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρ ⊆ Ω)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius))
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
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    (hzV : (z₀ 0, spectatorCenter z₀) ∈ V)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {cap : ℝ} (hcap : 0 < cap) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ a b : ℝ, ∃ ha : 0 < a, ∃ hcell : 4 * a < 1 / 2, ∃ hb : 0 < b,
      a < cap ∧ ∃ χinitial : ContDiffBump (0 : CarrierVariable n),
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧
    ∃ Cbound Lbound : ℕ → ℝ, (∀ s, 0 ≤ Cbound s) ∧ (∀ s, 0 ≤ Lbound s) ∧
      ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      ∀ cσ : FlowConstruction.Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
        ((0 : Euclidean (n - 1)), zCell) Rc M τ row col (sourceDilation H.map σ),
      MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.2, transportPosition T cσ.Q p))
        (supportedChart z₀ a) (interior {q | χinitial q = 1}) ∧
      let d := data T cσ.Q (sourceDilation H.map σ) row col cσ.forward cσ.inverse
        (fun _ ↦ σ) ha hcell (angularMask z₀ (NormedSpace.normalize ηb) ha hb)
        FixedCutoffs.highFrequency
      let e := normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse
        (fun _ ↦ 1) ha hcell (angularMask z₀ (NormedSpace.normalize ηb) ha hb)
        FixedCutoffs.highFrequency σ
      carrierKernel d = carrierKernel e ∧
      ∃ A : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ w, A.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) ∧
        (∀ B : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) → B = A) ∧
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
          MemRawSobolev s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ∧
          rawSobolevNorm s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            Cbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∃ hraw : ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          MemRawSobolev s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)),
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          rawSobolevNorm s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            (2 * Cbound s) * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) (s + 1),
          let f := (carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 (s + 1) w)
          let hf := (hraw (s + 1) w).mono (by omega : 1 ≤ s + 1)
          MemPhysicalSobolev s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha hb f hf)) ∧
          MemPhysicalSobolev s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha hb χinitial f hf)) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha hb f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha hb χinitial f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) := by
  obtain ⟨a, b, ha, hb, hacap, χinitial, σ₀, hσ₀, hσ₁, hsubmasks⟩ :=
    exists_retained_source_rawAdjoint_for_submasks H hP T hUH hbounded hΩ hKΩ hpatch
      hRc hτ hτR hbuffer hphysical c₀ htrans hR hRphysical hRU hV hVP hflow
      hz₀ hzV hk hinc hd hcap
  obtain ⟨hcell, Cbound, Lbound, hCbound, hLbound, hraw⟩ :=
    hsubmasks a b ha hb le_rfl le_rfl
  exact ⟨a, b, ha, hcell, hb, hacap, χinitial, σ₀, hσ₀, hσ₁,
    Cbound, Lbound, hCbound, hLbound, hraw⟩

end JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
