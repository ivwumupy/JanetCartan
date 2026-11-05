module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.MatchedSeedAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.MatchedCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedPrimitives
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.DensityFootpoint

/-!
# Primitive convergence and matched actual scalar contractions

For `app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`,
and `app:ch_osc:prop:osc-normal`, Step 4'. The primitive finite estimates use
the same constructed seed scalar as the matched positive-scale null flows.
A product buffer is chosen in their common inner cylinder, giving a single
compact ODE-footpoint range for all positive contractions. Consumer: the
finite source-family assembly and density composition at both endpoints.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open NullTransport ActualFlow FlowAmplitude ContinuumNormalReduction.TransportSymbol
open PositiveReference HamiltonPhase NormalizedBackground.SourceGeometry

/-- The actual seed scalar, finite primitive convergence and every positive
scalar contraction share one set of ODE witnesses. The fixed compact density
range is independent of scale; it concerns the ODE inverse, not Hamilton
transport. The frame threshold precedes the admitted seed and is consumed by
`exists_finite_same_seed_primitive_inputs`. Source:
`app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`. -/
theorem exists_retained_seed_matched_primitive_convergence {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U) :
    ∃ δ > (0 : ℝ), ∀ (F : Euclidean n → Euclidean N), ContDiff ℝ ∞ F →
      IsImmersionOn F U → HasFullNormalRankOn F U →
      ∀ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      Q.1 = ProjectedStressFrame.projectedStress F →
      (∀ x ∈ U, inducedMetric F x = 1) →
      (∀ v ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
        ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp v, T.data.adapted.normal⟫_ℝ ≠ 0) →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ z : CarrierParameter, parameter z ∈ parameterCube P.radius →
      ∃ row col : Fin n,
      ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
      ∃ R > (0 : ℝ), ∃ V : Set CarrierParameter, IsOpen V ∧ z ∈ V ∧
        R ≤ T.physicalRadius ∧ ball (0 : Euclidean n) R ⊆ U ∧
        V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2) ∧
      ∃ L : Set (Euclidean (n - 1) × Euclidean 3), IsCompact L ∧
        ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V) ∧
        MapsTo (densityFootpoint T Y) (ball 0 R ×ˢ V) L ∧
        (∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
          (densityFootpoint T Y p).2 = parameter p.2) ∧
        (∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0) ∧
        (∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
          0 < carrierScalarAmplitude T Q F row col Φ Y (fun _ ↦ 1) (p.1, parameter p.2)) ∧
        ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
          carrierScalarAmplitude T Q F row col Φ Y (fun _ ↦ 1) (p.1, parameter p.2) •
            carrierNullvector T Q col (p.1, parameter p.2)) (ball 0 R ×ˢ V) ∧
        ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
        (∀ σ : ℝ, 0 < σ → σ ≤ 1 →
          ∀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
            cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
              (Q - fun _ ↦ cubeStress n) < T.family.threshold},
            Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ) →
          ∃ Φσ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
            ContDiffOn ℝ ∞ (densityFootpoint T Yσ) (ball 0 R ×ˢ V) ∧
            (∀ m, cNorm (closedBall ((0 : Euclidean n), z) R) m
              (densityFootpoint T Yσ) ≤ B m) ∧
            MapsTo (densityFootpoint T Yσ) (ball 0 R ×ˢ V) L ∧
            (∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
              (densityFootpoint T Yσ p).2 = parameter p.2) ∧
            EqOn (densityFootpoint T Yσ) (densityFootpoint T (sourceTransportFlow Y σ))
              (ball 0 R ×ˢ V) ∧
            EqOn (fun p : Euclidean n × CarrierParameter ↦
                carrierScalarAmplitude T Qσ (sourceDilation F σ) row col Φσ Yσ (fun _ ↦ σ)
                  (p.1, parameter p.2))
              (fun p ↦ sourceAmplitude
                (carrierScalarAmplitude T Q F row col Φ Y (fun _ ↦ 1)) σ
                  (p.1, parameter p.2)) (ball 0 R ×ˢ V) ∧
            EqOn (fun p : Euclidean n × CarrierParameter ↦
                carrierScalarAmplitude T Qσ (sourceDilation F σ) row col Φσ Yσ (fun _ ↦ σ)
                  (p.1, parameter p.2) • carrierNullvector T Qσ col (p.1, parameter p.2))
              (fun p ↦ sourceAmplitude (fun w ↦ carrierScalarAmplitude T Q F row col Φ Y
                (fun _ ↦ 1) w • carrierNullvector T Q col w) σ (p.1, parameter p.2))
              (ball 0 R ×ˢ V) ∧
            ∀ D : CoefficientNormCharts n, D.field.carrier ⊆ ball 0 R ×ˢ V →
            ∀ (r : ℝ) (hr : 0 < r) (hcell : 4 * r < 1 / 2)
              (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ),
            let a := TransportKernel.coefficientsOfCarrier
              (data T Qσ (sourceDilation F σ) row col Φσ Yσ (fun _ ↦ σ)
                hr hcell angular high) (FixedCutoffs.physical hr 1)
            let b := fun s ↦ TransportKernel.coefficientsOfCarrier
              (normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1)
                hr hcell angular high s) (FixedCutoffs.physical hr 1)
            ∀ m : ℕ,
              cNorm D.field.carrier (m + 2)
                (CanonicalCarrier.transportPosition T Qσ - normalizedTransportPosition T Q 0) =
              cNorm D.field.carrier (m + 2)
                (normalizedTransportPosition T Q σ - normalizedTransportPosition T Q 0) ∧
              cNorm D.field.carrier m (a.normal - (b 0).normal) =
                cNorm D.field.carrier m ((b σ).normal - (b 0).normal) ∧
              cNorm D.field.carrier m (a.reduced - (b 0).reduced) =
                cNorm D.field.carrier m ((b σ).reduced - (b 0).reduced)) ∧
        ∀ (D : CoefficientNormCharts n), MapsTo Prod.snd D.field.carrier V →
        ∀ (r : ℝ) (hr : 0 < r) (hcell : 4 * r < 1 / 2)
          (angular : CarrierParameter → Euclidean (n - 1) → ℝ)
          (high : ℝ → ℝ) (measurement : Euclidean n → ℝ),
        let a := fun σ ↦ TransportKernel.coefficientsOfCarrier
          (normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) hr hcell angular high σ) measurement
        ∀ (m : ℕ) (ε : ℝ), 0 < ε → ∃ s > (0 : ℝ), s ≤ 1 ∧
          ∀ σ ∈ Ioc (0 : ℝ) s,
            cNorm D.field.carrier (m + 2)
              (normalizedTransportPosition T Q σ - normalizedTransportPosition T Q 0) +
            cNorm D.field.carrier m ((a σ).normal - (a 0).normal) +
            cNorm D.field.carrier m ((a σ).reduced - (a 0).reduced) < ε := by
  obtain ⟨δ, hδ, hseed⟩ := exists_retained_seed_matched_unit_transport (N := N) hn hP T hphysical
  refine ⟨δ, hδ, ?_⟩
  intro F hF hi hrank Q hQ hflat htrans hclose z hz
  obtain ⟨row, col, τ, R₀, hτ, hR₀, D₀, Φ, Y, _hD₀, hsmall, hphys, _, _, hY,
    _, hYU, hΦzero, hYΦ, _, _, hYz, _, _, hb, _, hpos, _, _, _, B, hB, hcurrent⟩ :=
    hseed F hF hi hrank Q hQ hflat htrans hclose (parameter z) hz
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let J : (Euclidean n × CarrierParameter) → Euclidean n × Euclidean 3 :=
    fun p ↦ (p.1, parameter p.2)
  have hJ : ContDiff ℝ ∞ J := contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)
  let W := Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), parameter z) (R₀ / 32)
  have hW : IsOpen ((densityCoordinates T) ⁻¹' W) :=
    (isOpen_Ioo.prod isOpen_ball).preimage (densityCoordinates T).continuous
  have hzW : ((0 : Euclidean n), z) ∈ (densityCoordinates T) ⁻¹' W := by
    change C (0, parameter z) ∈ Ioo (-τ) τ ×ˢ ball (0, parameter z) (R₀ / 32)
    simpa only [C, coordinates_apply, map_zero, Prod.fst_zero, Prod.snd_zero] using
      (show ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter z)) ∈
        Ioo (-τ) τ ×ˢ ball (0, parameter z) (R₀ / 32) from
          ⟨⟨neg_neg_of_pos hτ, hτ⟩, mem_ball_self (by positivity)⟩)
  obtain ⟨d, hd, hdball⟩ := Metric.isOpen_iff.mp hW (0, z) hzW
  let R := min (d / 2) T.physicalRadius
  let V := ball z R
  have hR : 0 < R := lt_min (half_pos hd) T.physicalRadius_pos
  have hmapsK : MapsTo (densityCoordinates T) (closedBall ((0 : Euclidean n), z) R) W := by
    intro p hp
    apply hdball
    exact (mem_closedBall.mp hp).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hd))
  have hKmaps : ball (0 : Euclidean n) R ×ˢ V ⊆ closedBall ((0 : Euclidean n), z) R := by
    intro p hp
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    exact ⟨(mem_ball.mp hp.1).le, (mem_ball.mp hp.2).le⟩
  have hmapsW : MapsTo (densityCoordinates T) (ball 0 R ×ˢ V) W :=
    fun _ hp ↦ hmapsK (hKmaps hp)
  have hmaps : MapsTo (densityCoordinates T) (ball 0 R ×ˢ V) D₀ :=
    fun _ hp ↦ hsmall (hmapsW hp)
  have hphys' : MapsTo J (ball 0 R ×ˢ V) (C ⁻¹' D₀) := fun _ hp ↦ hmaps hp
  have hzV : z ∈ V := mem_ball_self hR
  have hRU : ball (0 : Euclidean n) R ⊆ U := fun x hx ↦ (hphys (hmaps (show (x, z) ∈ ball (0 : Euclidean n) R ×ˢ V from ⟨hx, hzV⟩))).1
  have hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2) :=
    fun v hv ↦ (hphys (hmaps (show ((0 : Euclidean n), v) ∈ ball 0 R ×ˢ V from
      ⟨mem_ball_self hR, hv⟩))).2
  have hb' := hb.comp hJ.contDiffOn hphys'
  have hYzero (w) (hw : w ∈ V) : (densityFootpoint T Y (0, w)).1 = 0 := by
    have hh := hmapsW (show ((0 : Euclidean n), w) ∈ ball 0 R ×ˢ V from
      ⟨mem_ball_self hR, hw⟩)
    have hlabel : ((0 : Euclidean (n - 1)), parameter w) ∈
        ball (0, parameter z) (R₀ / 8) := by
      apply ball_subset_ball (show R₀ / 32 ≤ R₀ / 8 by linarith [hR₀])
      simpa [densityCoordinates, coordinates_apply] using hh.2
    have he := hYΦ _ hlabel 0 (show (0 : ℝ) ∈ Ioo (-τ) τ from
      ⟨neg_neg_of_pos hτ, hτ⟩)
    rw [hΦzero _ hlabel] at he
    simpa [densityFootpoint, densityCoordinates, coordinates_apply] using congrArg Prod.fst he
  let Kode := Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), parameter z) (R₀ / 8)
  have hKode : IsCompact Kode := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hWkode : W ⊆ Kode := fun q hq ↦
    ⟨Ioo_subset_Icc_self hq.1,
      closedBall_subset_closedBall (by linarith [hR₀]) (ball_subset_closedBall hq.2)⟩
  obtain ⟨A, hA, hbound⟩ := ConstructedCarrierJets.exists_cNorm_fixed_pullback_le
    (G := Euclidean (n - 1) × Euclidean 3) (isCompact_closedBall ((0 : Euclidean n), z) R)
    hKode (fun _ _ ↦ (densityCoordinates T).contDiff.contDiffAt)
    (fun _ hp ↦ hWkode (hmapsK hp))
  refine ⟨row, col, Φ, Y, R, hR, V, isOpen_ball, hzV, min_le_right _ _, hRU, hVP,
    closedBall (0, parameter z) (R₀ / 8), isCompact_closedBall _ _,
    hY.comp (densityCoordinates T).contDiff.contDiffOn hmaps,
    densityFootpoint_mapsTo_closedBall T hmaps hYU,
    fun p hp ↦ hYz _ (hmaps hp), hYzero, fun p hp ↦ (hpos _ (hmaps hp)).1, hb', fun m ↦ A m * B m, fun m ↦ mul_pos (hA m) (hB m), ?_, ?_⟩
  · intro σ hσ hσ1 Qσ hQσ
    obtain ⟨Dσ, Φσ, Yσ, _, hsmallσ, hYσ, hYbufferσ, hnormσ, hYUσ, hYzσ, _, _, _, _,
      hYmatch, hαmatch, hbmatch⟩ := hcurrent σ hσ hσ1 Qσ hQσ
    have hmapsσ : MapsTo (densityCoordinates T) (ball 0 R ×ˢ V) Dσ :=
      fun _ hp ↦ hsmallσ (hmapsW hp)
    have hYat (q) (hq : q ∈ Kode) : ContDiffAt ℝ ∞ Yσ q := by
      apply hYbufferσ.contDiffAt ((isOpen_Ioo.prod isOpen_ball).mem_nhds ?_)
      exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩,
        closedBall_subset_ball (by linarith [hR₀]) hq.2⟩
    refine ⟨Φσ, Yσ, hYσ.comp (densityCoordinates T).contDiff.contDiffOn hmapsσ, ?_,
      densityFootpoint_mapsTo_closedBall T hmapsσ hYUσ,
      fun p hp ↦ hYzσ _ (hmapsσ hp), fun p hp ↦ hYmatch (hmapsσ hp),
      fun p hp ↦ hαmatch (hmapsσ hp), fun p hp ↦ hbmatch (hmapsσ hp), ?_⟩
    · intro m
      have hle : cNorm Kode m Yσ ≤ B m := by
        have := cNorm_nonneg Kode m Φσ
        have := hnormσ m
        linarith
      exact (hbound Yσ hYat m).trans (mul_le_mul_of_nonneg_left hle (hA m).le)
    · intro D hD r hr hcell angular high
      dsimp only
      intro m
      have hfields (p) (hp : p ∈ ball (0 : Euclidean n) R ×ˢ V) :=
        coefficientsOfCarrier_current_eq_normalized hP T Q Qσ hF hrank hphysical
          hQ htrans hσ hσ1 hQσ row col Φ Y Φσ Yσ hr hcell angular high
          (ball_subset_ball (min_le_right _ _) hp.1)
          (fun i ↦ (hVP hp.2 i).trans (by linarith [hP.1])) (hbmatch (hmapsσ hp))
      have htransport := (SourceMatching.current_transportPosition_source_dilation_on_patch
        T Q Qσ hF hrank hphysical hQ htrans hσ hσ1 hQσ).1
      refine ⟨?_, ?_, ?_⟩
      · apply GeometricProfile.cNorm_eq_of_eventuallyEq
        intro p hp
        filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds (hD hp)] with q hq
        have he := htransport (show q ∈ ball (0 : Euclidean n) T.physicalRadius ×ˢ
            (parameter ⁻¹' parameterInterior (2 * P.radius)) from
          ⟨ball_subset_ball (min_le_right _ _) hq.1,
            fun i ↦ (hVP hq.2 i).trans (by linarith [hP.1])⟩)
        change CanonicalCarrier.transportPosition T Qσ q =
          normalizedTransportPosition T Q σ q at he
        exact congrArg (fun v ↦ v - normalizedTransportPosition T Q 0 q) he
      · apply GeometricProfile.cNorm_eq_of_eventuallyEq
        intro p hp
        filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds (hD hp)] with q hq
        exact congrArg (fun v ↦ v - _) (hfields q hq).1
      · apply GeometricProfile.cNorm_eq_of_eventuallyEq
        intro p hp
        filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds (hD hp)] with q hq
        exact congrArg (fun v ↦ v - _) (hfields q hq).2
  intro D hDV r hr hcell angular high measurement
  dsimp only
  intro m ε hε
  obtain ⟨hn, hq⟩ := tendsto_normalizedCarrierData_coefficients_sub_cNorm T Q F row col Φ Y
    (fun _ ↦ 1) hr hcell angular high measurement hP hQ hF.contDiffOn hi hrank
    hR (min_le_right _ _) hRU isOpen_ball hVP hb' D hDV m
  have ht := tendsto_normalizedTransportPosition_sub_cNorm T Q hP
    (isCompact_closedBall D.field.center D.field.radius) (fun p hp ↦ hVP (hDV hp)) m
  have hsum := (ht.add hn).add hq
  rw [add_zero, add_zero] at hsum
  obtain ⟨e, he, hsmall⟩ := Metric.mem_nhds_iff.mp (hsum.eventually (gt_mem_nhds hε))
  refine ⟨min (e / 2) 1, lt_min (half_pos he) zero_lt_one, min_le_right _ _, ?_⟩
  intro σ hσ
  apply hsmall
  rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ.1]
  exact (hσ.2.trans (min_le_left _ _)).trans_lt (half_lt_self he)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
