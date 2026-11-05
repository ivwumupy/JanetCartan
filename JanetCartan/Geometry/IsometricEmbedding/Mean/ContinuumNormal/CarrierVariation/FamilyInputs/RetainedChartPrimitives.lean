module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.SourceMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.MatchedCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedPrimitives
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Boxes

/-!
# Source primitive convergence on supplied retained leading charts

The seed is the supplied comparison chart, with its original selected minor
and actual scalar ODE maps. A fixed product buffer lies in every chart's
common inner cylinder. ODE uniqueness identifies each positive contraction;
the existing normalized coefficient limits then give the literal finite-norm
estimate. Consumer: the initialized source weighted comparison. Sources:
`app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`,
and `app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier FrozenModel PositiveReference PositiveReference.FlowConstruction
open FullPhaseCharts.ActualComparison
open NormalizedBackground.SourceGeometry ContinuumNormalReduction.TransportSymbol HamiltonPhase

/-- Finite source-to-zero convergence for the literal retained carrier fields.
The reference and every current chart have the SAME supplied minor, coefficient
ball and flow radius. No new seed or scalar is selected. The positive threshold
controls the sum of the `C^(m+2)` transport error and both `C^m` coefficient
errors. The fixed compact range and both ODE-label identities remain available
for the wider-density composition (`bg-full-complex-amplitude`). -/
theorem exists_retained_chart_source_primitive_convergence
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {z₀ : Euclidean 3} {ρ Rc B τ : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), z₀) ρ ⊆ Ω)
    (hΩpatch : Ω ⊆ (U ∩ ball 0 T.physicalRadius) ×ˢ parameterInterior (3 * P.radius / 2))
    (hRc : 0 < Rc) (hτ : 0 < τ) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc)
      (closedBall ((0 : Euclidean n), z₀) ρ))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (c₀ : Chart T Ω (closedBall ((0 : Euclidean n), z₀) ρ)
      ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU c₀.Q.1 c₀.Q.2.1).hp q, T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1) :
    ∃ R > (0 : ℝ), ∃ V : Set CarrierParameter, IsOpen V ∧
      (z₀ 0, spectatorCenter z₀) ∈ V ∧ R ≤ T.physicalRadius ∧
      ball (0 : Euclidean n) R ⊆ U ∧
      V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2) ∧
      ContDiffOn ℝ ∞ (densityFootpoint T c₀.inverse) (ball 0 R ×ˢ V) ∧
      MapsTo (densityFootpoint T c₀.inverse) (ball 0 R ×ˢ V)
        (closedBall ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) ∧
      (∀ z ∈ V, (densityFootpoint T c₀.inverse (0, z)).1 = 0) ∧
      (∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
        (densityFootpoint T c₀.inverse p).2 = parameter p.2) ∧
      ∀ D : CoefficientNormCharts n, D.field.carrier ⊆ ball (0 : Euclidean n) R ×ˢ V →
      ∀ (rm : ℝ) (hrm : 0 < rm) (hcell : 4 * rm < 1 / 2)
        (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ),
      let a₀ := TransportKernel.coefficientsOfCarrier
        (normalizedCarrierData T c₀.Q F row col c₀.forward c₀.inverse (fun _ ↦ 1)
          hrm hcell angular high 0) (FixedCutoffs.physical hrm 1)
      ∀ m : ℕ, ∀ tol > (0 : ℝ), ∃ s > (0 : ℝ), s ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) s,
      ∀ cσ : Chart T Ω (closedBall ((0 : Euclidean n), z₀) ρ)
        ((0 : Euclidean (n - 1)), z₀) Rc B τ row col (sourceDilation F σ),
      EqOn (densityFootpoint T cσ.inverse)
        (densityFootpoint T (sourceTransportFlow c₀.inverse σ)) (ball 0 R ×ˢ V) ∧
      let aσ := TransportKernel.coefficientsOfCarrier
        (data T cσ.Q (sourceDilation F σ) row col cσ.forward cσ.inverse (fun _ ↦ σ)
          hrm hcell angular high) (FixedCutoffs.physical hrm 1)
      cNorm D.field.carrier (m + 2)
          (transportPosition T cσ.Q - normalizedTransportPosition T c₀.Q 0) +
        cNorm D.field.carrier m (aσ.normal - a₀.normal) +
        cNorm D.field.carrier m (aσ.reduced - a₀.reduced) < tol := by
  let z : CarrierParameter := (z₀ 0, spectatorCenter z₀)
  have hz : parameter z = z₀ := by
    ext i
    fin_cases i <;> rfl
  let W := Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 32)
  have hW : IsOpen ((densityCoordinates T) ⁻¹' W) :=
    (isOpen_Ioo.prod isOpen_ball).preimage (densityCoordinates T).continuous
  have hzW : ((0 : Euclidean n), z) ∈ (densityCoordinates T) ⁻¹' W := by
    change coordinates (adaptedCoordinates T.data.adapted) (0, parameter z) ∈ W
    simpa only [coordinates_apply, map_zero, Prod.fst_zero, Prod.snd_zero, hz] using
      (show ((0 : ℝ), ((0 : Euclidean (n - 1)), z₀)) ∈ W from
        ⟨⟨neg_neg_of_pos hτ, hτ⟩, mem_ball_self (by positivity)⟩)
  obtain ⟨d, hd, hdball⟩ := Metric.isOpen_iff.mp hW (0, z) hzW
  let R := min (d / 2) T.physicalRadius
  let V := ball z R
  have hR : 0 < R := lt_min (half_pos hd) T.physicalRadius_pos
  have hmapsW : MapsTo (densityCoordinates T) (ball 0 R ×ˢ V) W := by
    intro p hp
    apply hdball
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_ball.mp hp.1).trans_le ((min_le_left _ _).trans (half_le_self hd.le)),
      (mem_ball.mp hp.2).trans_le ((min_le_left _ _).trans (half_le_self hd.le))⟩
  have hmaps := fun p hp ↦ c₀.small_subset (hmapsW (x := p) hp)
  have hphys (p) (hp : p ∈ ball (0 : Euclidean n) R ×ˢ V) :
      (p.1, parameter p.2) ∈ Ω := by
    have hh := c₀.domain_coefficients (hmaps p hp)
    change (coordinates (adaptedCoordinates T.data.adapted)).symm
      (coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) ∈ Ω at hh
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
  have hRU : ball (0 : Euclidean n) R ⊆ U :=
    fun x hx ↦ (hΩpatch (hphys (x, z) ⟨hx, mem_ball_self hR⟩)).1.1
  have hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2) :=
    fun w hw ↦ (hΩpatch (hphys (0, w) ⟨mem_ball_self hR, hw⟩)).2
  obtain ⟨_, hb, _, _, _, _, _, _⟩ :=
    c₀.scalar_spec hτ (fun _ ↦ 1) contDiffOn_const (fun _ _ ↦ zero_lt_one)
  have hb' := hb.comp
    (contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)).contDiffOn hmaps
  have hYzero (w) (hw : w ∈ V) : (densityFootpoint T c₀.inverse (0, w)).1 = 0 := by
    have hh := hmapsW (show ((0 : Euclidean n), w) ∈ ball 0 R ×ˢ V from
      ⟨mem_ball_self hR, hw⟩)
    have hlabel : ((0 : Euclidean (n - 1)), parameter w) ∈
        ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8) := by
      apply ball_subset_ball (show Rc / 32 ≤ Rc / 8 by linarith)
      simpa [densityCoordinates, coordinates_apply] using hh.2
    have he := c₀.inverse_forward _ hlabel 0 ⟨neg_neg_of_pos hτ, hτ⟩
    rw [c₀.initial _ hlabel] at he
    simpa [densityFootpoint, densityCoordinates, coordinates_apply] using congrArg Prod.fst he
  refine ⟨R, hR, V, isOpen_ball, mem_ball_self hR, min_le_right _ _, hRU, hVP,
    c₀.inverse_smooth.comp (densityCoordinates T).contDiff.contDiffOn hmaps,
    densityFootpoint_mapsTo_closedBall T hmaps c₀.inverse_range,
    hYzero, fun p hp ↦ c₀.inverse_parameter _ (hmaps p hp), ?_⟩
  intro D hD rm hrm hcell angular high
  dsimp only
  intro m tol htol
  obtain ⟨hn, hq⟩ := tendsto_normalizedCarrierData_coefficients_sub_cNorm T c₀.Q F row col
    c₀.forward c₀.inverse (fun _ ↦ 1) hrm hcell angular high (FixedCutoffs.physical hrm 1)
    hP c₀.frame_eq hF.contDiffOn hi hrank hR (min_le_right _ _) hRU isOpen_ball hVP
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
      hrm hcell angular high (ball_subset_ball (min_le_right _ _) hp.1)
      (fun i ↦ (hVP hp.2 i).trans (by linarith [hP.1])) (hnull (hmapsσ p hp))
  have htransport := (SourceMatching.current_transportPosition_source_dilation_on_patch
    T c₀.Q cσ.Q hF hrank hphysical c₀.frame_eq htrans hσ.1 hσ1 cσ.frame_eq).1
  have heqT : cNorm D.field.carrier (m + 2)
      (transportPosition T cσ.Q - normalizedTransportPosition T c₀.Q 0) =
      cNorm D.field.carrier (m + 2)
      (normalizedTransportPosition T c₀.Q σ - normalizedTransportPosition T c₀.Q 0) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro p hp
    filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds (hD hp)] with q hq
    exact congrArg (fun v ↦ v - normalizedTransportPosition T c₀.Q 0 q)
      (htransport (show q ∈ ball (0 : Euclidean n) T.physicalRadius ×ˢ
          (parameter ⁻¹' parameterInterior (2 * P.radius)) from
        ⟨ball_subset_ball (min_le_right _ _) hq.1,
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
    filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds (hD hp)] with q hq
    exact congrArg (fun v ↦ v - (an 0).normal q) (hfields q hq).1
  have heqR : cNorm D.field.carrier m (a.reduced - (an 0).reduced) =
      cNorm D.field.carrier m ((an σ).reduced - (an 0).reduced) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro p hp
    filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds (hD hp)] with q hq
    exact congrArg (fun v ↦ v - (an 0).reduced q) (hfields q hq).2
  rw [heqT, heqN, heqR]
  apply hsmall
  rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ.1]
  exact (hσ.2.trans (min_le_left _ _)).trans_lt (half_lt_self he)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
