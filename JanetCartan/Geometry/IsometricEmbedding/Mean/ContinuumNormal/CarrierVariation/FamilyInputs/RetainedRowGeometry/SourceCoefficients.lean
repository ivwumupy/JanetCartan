module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartPrimitives
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Comparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.KernelCoefficients

/-!
# Source coefficients on the original retained output cylinder

The comparison product may be centered at any incidence point of the retained
cell. The same original output cylinder contains every one of its points,
so the supplied seed and all contracted charts are compared there without
replacing the masks by a neighborhood of the ODE cell center.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier FrozenModel PositiveReference PositiveReference.FlowConstruction
open FullPhaseCharts.ActualComparison
open NormalizedBackground.SourceGeometry ContinuumNormalReduction.TransportSymbol HamiltonPhase
open ContinuumRow.CanonicalConic

/-- The original comparison-cell inclusion supplies every product-domain
premise of `exists_retained_chart_source_primitive_convergence_on_outputCylinder`.
The physical radius, carrier labels and output cylinder are deduced on the
ENTIRE coefficient product, with distinct incidence and ODE centers. Its
producers are the original cell and phase inclusions in
`ChartCenters.CarrierData` and `exists_original_outputCylinder_region`
applied to the retained comparison-radius bound. No detector support is reduced (`app:ch_background:eq:bg-Psi`,
`app:ch_background:prop:bg-normalized`). -/
theorem retained_coefficientDomain_source_buffers {n : ℕ} (hn : 0 < n)
    {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {zRoot zCell : Euclidean 3} {r a Rc τ : ℝ} (hr : 0 < r) (ha : 0 < a)
    {E : Set (Euclidean n × CarrierParameter)}
    (houter : coefficientDomain zRoot r a ⊆ E)
    (hpatch : E ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    (houtput : MapsTo (densityCoordinates T) E
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ)) :
    a ≤ T.physicalRadius ∧ ball (0 : Euclidean n) a ⊆ U ∧
    (ball (zRoot 0) r ×ˢ ball (spectatorCenter zRoot) a ⊆
      parameter ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    MapsTo (densityCoordinates T)
      (ball (0 : Euclidean n) a ×ˢ
        (ball (zRoot 0) r ×ˢ ball (spectatorCenter zRoot) a))
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hphysicalRadius := T.physicalRadius_pos
  have hball : ball (0 : Euclidean n) a ⊆ U ∩ ball 0 T.physicalRadius := by
    intro x hx
    exact (hpatch (houter (show (x, (zRoot 0, spectatorCenter zRoot)) ∈
      coefficientDomain zRoot r a from ⟨hx, mem_ball_self hr, mem_ball_self ha⟩))).1
  have hrad : a ≤ T.physicalRadius := by
    by_contra h
    have haR : T.physicalRadius < a := lt_of_not_ge h
    obtain ⟨x, hx⟩ := exists_norm_eq (Euclidean n)
      (show 0 ≤ (a + T.physicalRadius) / 2 by positivity)
    have hxa : x ∈ ball (0 : Euclidean n) a := by
      rw [mem_ball_zero_iff, hx]
      linarith
    have hxR := mem_ball_zero_iff.mp (hball hxa).2
    rw [hx] at hxR
    linarith
  exact ⟨hrad, hball.trans inter_subset_left,
    fun z hz ↦ (hpatch (houter (show ((0 : Euclidean n), z) ∈
      coefficientDomain zRoot r a from ⟨mem_ball_self ha, hz⟩))).2,
    houtput.mono_left houter⟩

/-- The actual retained source transport, normal and reduced detector converge
on a prescribed coefficient chart inside the ORIGINAL output cylinder. The
same supplied minor and forward/inverse ODE charts are used throughout. The
carrier region need not contain, or be centered at, `zCell`.

`exists_original_outputCylinder_region` supplies the output-cylinder
containment from the original cell and retained comparison-radius bound;
the full coefficient product therefore supplies `hflow`. `exists_retained_mean_flow_buffers` supplies the
corresponding product inclusions for the mean. This result discharges the
primitive source limits on these products, instead of choosing a new
neighborhood around the ODE cell center. The arbitrary initial-density
comparison remains a subsequent use of `WideDensity`.

Consumer: the SAME-row weighted amplitude comparison in `FamilyInputs`.
Sources: `app:ch_background:eq:bg-Nsigma`,
`app:ch_background:prop:bg-normalized`, and `app:ch_osc:prop:osc-normal`,
Step 4'. -/
theorem exists_retained_chart_source_primitive_convergence_on_outputCylinder
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρ Rc B τ : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρ ⊆ Ω)
    (hΩpatch : Ω ⊆ (U ∩ ball 0 T.physicalRadius) ×ˢ parameterInterior (3 * P.radius / 2))
    (hRc : 0 < Rc) (hτ : 0 < τ) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρ))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (c₀ : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc B τ row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU c₀.Q.1 c₀.Q.2.1).hp q, T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    {R : ℝ} {V : Set CarrierParameter} (hR : 0 < R)
    (hRphysical : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hV : IsOpen V) (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ))
    (D : CoefficientNormCharts n) (hD : D.field.carrier ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (rm : ℝ) (hrm : 0 < rm) (hcell : 4 * rm < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ) :
    ContDiffOn ℝ ∞ (densityFootpoint T c₀.inverse) (ball 0 R ×ˢ V) ∧
    MapsTo (densityFootpoint T c₀.inverse) (ball 0 R ×ˢ V)
      (closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8)) ∧
    (∀ z ∈ V, (densityFootpoint T c₀.inverse (0, z)).1 = 0) ∧
    (∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T c₀.inverse p).2 = parameter p.2) ∧
    let a₀ := TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T c₀.Q F row col c₀.forward c₀.inverse (fun _ ↦ 1)
        hrm hcell angular high 0) (FixedCutoffs.physical hrm 1)
    ∀ m : ℕ, ∀ tol > (0 : ℝ), ∃ s > (0 : ℝ), s ≤ 1 ∧
    ∀ σ ∈ Ioc (0 : ℝ) s,
    ∀ cσ : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc B τ row col (sourceDilation F σ),
    EqOn (densityFootpoint T cσ.inverse)
      (densityFootpoint T (sourceTransportFlow c₀.inverse σ)) (ball 0 R ×ˢ V) ∧
    let aσ := TransportKernel.coefficientsOfCarrier
      (data T cσ.Q (sourceDilation F σ) row col cσ.forward cσ.inverse (fun _ ↦ σ)
        hrm hcell angular high) (FixedCutoffs.physical hrm 1)
    cNorm D.field.carrier (m + 2)
        (transportPosition T cσ.Q - normalizedTransportPosition T c₀.Q 0) +
      cNorm D.field.carrier m (aσ.normal - a₀.normal) +
      cNorm D.field.carrier m (aσ.reduced - a₀.reduced) < tol := by
  have hmapsW : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), zCell) (Rc / 32)) :=
    hflow.mono_right (outputCylinder_spec hRc hτ).2
  have hmaps := fun p hp ↦ c₀.small_subset (hmapsW (x := p) hp)
  obtain ⟨_, hb, _, _, _, _, _, _⟩ :=
    c₀.scalar_spec hτ (fun _ ↦ 1) contDiffOn_const (fun _ _ ↦ zero_lt_one)
  have hb' := hb.comp
    (contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)).contDiffOn hmaps
  have hYzero (z) (hz : z ∈ V) : (densityFootpoint T c₀.inverse (0, z)).1 = 0 := by
    have hh := hmapsW (show ((0 : Euclidean n), z) ∈ ball 0 R ×ˢ V from
      ⟨mem_ball_self hR, hz⟩)
    have hlabel : ((0 : Euclidean (n - 1)), parameter z) ∈
        ball ((0 : Euclidean (n - 1)), zCell) (Rc / 8) := by
      apply ball_subset_ball (show Rc / 32 ≤ Rc / 8 by linarith)
      simpa [densityCoordinates, coordinates_apply] using hh.2
    have he := c₀.inverse_forward _ hlabel 0 ⟨neg_neg_of_pos hτ, hτ⟩
    rw [c₀.initial _ hlabel] at he
    simpa [densityFootpoint, densityCoordinates, coordinates_apply] using congrArg Prod.fst he
  refine ⟨c₀.inverse_smooth.comp (densityCoordinates T).contDiff.contDiffOn hmaps,
    densityFootpoint_mapsTo_closedBall T hmaps c₀.inverse_range, hYzero,
    fun p hp ↦ c₀.inverse_parameter _ (hmaps p hp), ?_⟩
  dsimp only
  intro m tol htol
  obtain ⟨hn, hq⟩ := tendsto_normalizedCarrierData_coefficients_sub_cNorm T c₀.Q F row col
    c₀.forward c₀.inverse (fun _ ↦ 1) hrm hcell angular high (FixedCutoffs.physical hrm 1)
    hP c₀.frame_eq hF.contDiffOn hi hrank hR hRphysical hRU hV hVP
    hb' D (fun p hp ↦ (hD hp).2) m
  have ht := tendsto_normalizedTransportPosition_sub_cNorm T c₀.Q hP
    (isCompact_closedBall D.field.center D.field.radius) (fun p hp ↦ hVP (hD hp).2) m
  have hsum := (ht.add hn).add hq
  rw [add_zero, add_zero] at hsum
  obtain ⟨e, he, hsmall⟩ := Metric.mem_nhds_iff.mp (hsum.eventually (gt_mem_nhds htol))
  refine ⟨min (e / 2) 1, lt_min (half_pos he) zero_lt_one, min_le_right _ _, ?_⟩
  intro σ hσ cσ
  have hσ1 : σ ≤ 1 := hσ.2.trans (min_le_right _ _)
  have hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius) := by
    intro w hw
    exact ⟨(hΩpatch hw).1.2, fun i ↦ (hΩpatch hw).2 i |>.le.trans (by linarith [hP.1])⟩
  obtain ⟨_, hfoot, _, hnull, _⟩ := RetainedLeading.retained_charts_source_dilation
    T hΩ hKΩ hpatch hRc hτ hτR hbuffer hF hrank hphysical c₀ htrans hflat hσ.1 hσ1 cσ
  have hmapsσ := fun p hp ↦ cσ.small_subset (hmapsW (x := p) hp)
  refine ⟨fun p hp ↦ hfoot (hmapsσ p hp), ?_⟩
  have hfields (p) (hp : p ∈ ball (0 : Euclidean n) R ×ˢ V) :=
    coefficientsOfCarrier_current_eq_normalized hP T c₀.Q cσ.Q hF hrank hphysical
      c₀.frame_eq htrans hσ.1 hσ1 cσ.frame_eq row col c₀.forward c₀.inverse cσ.forward cσ.inverse
      hrm hcell angular high (ball_subset_ball hRphysical hp.1)
      (fun i ↦ (hVP hp.2 i).trans (by linarith [hP.1])) (hnull (hmapsσ p hp))
  have htransport := (SourceMatching.current_transportPosition_source_dilation_on_patch
    T c₀.Q cσ.Q hF hrank hphysical c₀.frame_eq htrans hσ.1 hσ1 cσ.frame_eq).1
  have heqT : cNorm D.field.carrier (m + 2)
      (transportPosition T cσ.Q - normalizedTransportPosition T c₀.Q 0) =
      cNorm D.field.carrier (m + 2)
      (normalizedTransportPosition T c₀.Q σ - normalizedTransportPosition T c₀.Q 0) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro p hp
    filter_upwards [(isOpen_ball.prod hV).mem_nhds (hD hp)] with q hq
    exact congrArg (fun v ↦ v - normalizedTransportPosition T c₀.Q 0 q)
      (htransport (show q ∈ ball (0 : Euclidean n) T.physicalRadius ×ˢ
          (parameter ⁻¹' parameterInterior (2 * P.radius)) from
        ⟨ball_subset_ball hRphysical hq.1,
          fun i ↦ (hVP hq.2 i).trans (by linarith [hP.1])⟩))
  let a := TransportKernel.coefficientsOfCarrier
    (data T cσ.Q (sourceDilation F σ) row col cσ.forward cσ.inverse (fun _ ↦ σ)
      hrm hcell angular high) (FixedCutoffs.physical hrm 1)
  let an := fun s ↦ TransportKernel.coefficientsOfCarrier
    (normalizedCarrierData T c₀.Q F row col c₀.forward c₀.inverse (fun _ ↦ 1)
      hrm hcell angular high s) (FixedCutoffs.physical hrm 1)
  have heqN : cNorm D.field.carrier m (a.normal - (an 0).normal) =
      cNorm D.field.carrier m ((an σ).normal - (an 0).normal) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro p hp
    filter_upwards [(isOpen_ball.prod hV).mem_nhds (hD hp)] with q hq
    exact congrArg (fun v ↦ v - (an 0).normal q) (hfields q hq).1
  have heqR : cNorm D.field.carrier m (a.reduced - (an 0).reduced) =
      cNorm D.field.carrier m ((an σ).reduced - (an 0).reduced) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro p hp
    filter_upwards [(isOpen_ball.prod hV).mem_nhds (hD hp)] with q hq
    exact congrArg (fun v ↦ v - (an 0).reduced q) (hfields q hq).2
  rw [heqT, heqN, heqR]
  apply hsmall
  rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ.1]
  exact (hσ.2.trans (min_le_left _ _)).trans_lt (half_lt_self he)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
