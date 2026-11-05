module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedChartFamily.CoefficientBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.Buffers
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.UniformFlow
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.TransportProfiles.LocalBounds

/-!
# Carrier flow bounds before geometric budgets

The full-modulation compatibility buffer in `main:prop:current-scale` needs a
flow C1 bound before source-dependent immersion budgets. This retains the
geometry-independent direction bound from the coefficient producer through the
same actual-flow construction used by `exists_local_positive_amplitude_before_geometry`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.CurrentCoefficientProfiles
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame NullTransport ActualFlow FlowAmplitude

/-- Choose the centered coefficient domain and doubled frozen-minor buffer
at the original cell selection. Source contraction preserves the centered
spatial balls; the compact set itself need not be invariant. All evidence
uses the SAME minor, domain, radii and maps.

The carrier minor, coefficient domain, compact buffer, direction bound and
exact existence time precede all immersion budgets. The joint conclusion retains
the primitive coefficient and ODE evidence for these very same maps, consumed by
`PositiveReference.FlowConstruction.Chart` through the retained-leading family
(`app:ch_waves:thm:leading`, `app:ch_background:prop:bg-frame`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_carrier_flow_before_geometry_with_source_geometry {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius) :
    ∃ row col : Fin n, ∃ ρ R η τ g Mc : ℝ,
    ∃ Ωc : Set (Euclidean n × Euclidean 3), ∃ Bc μc : ℝ,
      (0 < μc ∧
        (∀ σ ∈ Ioc (0 : ℝ) 1,
          MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (σ • w.1, w.2)) Ωc Ωc) ∧
        closedBall ((0 : Euclidean n), z) (2 * ρ) ⊆ Ωc ∧
        closedBall ((0 : Euclidean n), z) (2 * ρ) ⊆
          (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
            parameterInterior (3 * P.radius / 2) ∧
        MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) (2 * ρ))
          (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
        ∀ w ∈ closedBall ((0 : Euclidean n), z) (2 * ρ),
          2 * μc ≤ |(cubePencil (P.toFun w.2)).adjugate row col|) ∧
      0 < ρ ∧ 0 < R ∧ 0 < η ∧ 0 < τ ∧ 0 < g ∧ 0 < Mc ∧
      MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
        (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
        (closedBall ((0 : Euclidean n), z) ρ) ∧ τ ≤ R / 16 ∧
      (0 < ρ ∧ 0 < Bc ∧ 0 < g ∧ IsOpen Ωc ∧
        closedBall ((0 : Euclidean n), z) ρ ⊆ Ωc ∧
        Ωc ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
          parameterInterior (3 * P.radius / 2) ∧
        MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) ρ)
          (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
        MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
          (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
          (closedBall ((0 : Euclidean n), z) ρ) ∧
        τ = existenceTime R (NullTransport.ActualFlow.liftedLowBound T Bc) / 4 ∧
        τ ≤ R / 16) ∧
      ∀ (C₀ κmet κnormal : ℝ), 0 < κmet → 0 < κnormal →
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let e := adaptedCoordinates T.data.adapted
        let C := coordinates (Z := Euclidean 3) e
        let I := Ioo (-τ) τ
        let L := ball ((0 : Euclidean (n - 1)), z) (R / 8)
        ∃ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          (ContDiffOn ℝ ∞ (carrierNullvector T Q col) Ωc ∧
            ContDiffOn ℝ ∞ (carrierConullvector T Q row) Ωc ∧
            ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ωc ∧
            ContDiffOn ℝ ∞ (carrierTransportPotential T Q F row col) Ωc ∧
            cNorm (closedBall ((0 : Euclidean n), z) ρ) 1
              (carrierTransportDirection T Q row col) ≤ Bc ∧
            (∀ w ∈ Ωc, ∀ i, (Q.1 w.1 i).IsSymm) ∧
            (∀ w ∈ Ωc,
              carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
              reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
                (fun j ↦ carrierNullvector T Q col w j) = 0 ∧
              carrierConullvector T Q row w ᵥ*
                reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
              g ≤ |carrierAdaptedDenominator T Q row col w| ∧
              carrierAdaptedDenominator T Q row col w ≠ 0 ∧
              |(carrierAdaptedDenominator T Q row col w)⁻¹| ≤ g⁻¹) ∧
            D = (fun q ↦ (q.1, Φ q)) ''
              (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
            D ⊆ C.symm ⁻¹' Ωc ∧ C ⁻¹' D ⊆ Ωc ∧
            C ⁻¹' D ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
              parameterInterior (3 * P.radius / 2) ∧
            ContDiffOn ℝ ∞ Φ
              (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
            ContDiffOn ℝ ∞ Y D ∧
            (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8),
              ∀ t ∈ Ioo (-τ) τ, (Φ (t, p)).2 = p.2) ∧
            (∀ q ∈ D, (Y q).2 = q.2.2) ∧
            ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ
              ball ((0 : Euclidean (n - 1)), z) (R / 4))) ∧
          IsOpen D ∧
          I ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 32) ⊆ D ∧
          D ⊆ I ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 4) ∧
          C ⁻¹' D ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
            parameterInterior (3 * P.radius / 2) ∧
          ContDiffOn ℝ ∞ Φ (I ×ˢ L) ∧ ContDiffOn ℝ ∞ Y D ∧
          MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ L) D ∧
          MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ L) ∧
          (∀ p ∈ L, Φ (0, p) = p) ∧
          (∀ p ∈ L, ∀ t ∈ I, Y (t, Φ (t, p)) = p) ∧
          (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
          (∀ p ∈ L, ∀ t ∈ I, (Φ (t, p)).2 = p.2) ∧
          (∀ q ∈ D, (Y q).2 = q.2.2) ∧
          (∀ p ∈ L, ∀ t ∈ I, HasDerivAt (fun s ↦ Φ (s, p))
            ((e (carrierTransportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
          ContDiffOn ℝ ∞ Φ
            (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 4)) ∧
          cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) 1 Φ ≤ Mc ∧
          (∀ w ∈ C ⁻¹' D, g ≤ |carrierAdaptedDenominator T Q row col w|) := by
  obtain ⟨δ, μ, κ, hδ, hμ, hκ, V, hV, hcover, hfrozen, hcoeff⟩ :=
    exists_transport_coefficient_bounds_before_geometry_with_frozen_minors (N := N) hn hP T hK hKU hball
  obtain ⟨row, hrow⟩ := mem_iUnion.mp (hcover hz)
  obtain ⟨col, hcol⟩ := mem_iUnion.mp hrow
  let Ω₀ := (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
    (parameterInterior (3 * P.radius / 2) ∩ V row col)
  let Ω := (ball (0 : Euclidean n) T.physicalRadius ∩
    ball (0 : Euclidean n) T.data.localReference.stateRadius) ×ˢ
    (parameterInterior (3 * P.radius / 2) ∩ V row col)
  have hΩ : IsOpen Ω := (isOpen_ball.inter isOpen_ball).prod
    ((isOpen_parameterInterior _).inter (hV row col))
  have hstate : ball (0 : Euclidean n) T.data.localReference.stateRadius ⊆
      interior K := interior_maximal (ball_subset_closedBall.trans hball) isOpen_ball
  have hΩ₀ : Ω ⊆ Ω₀ := fun _ hw ↦ ⟨⟨hw.1.1, hstate hw.1.2⟩, hw.2⟩
  have hphysical : Ω ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
      parameterInterior (3 * P.radius / 2) :=
    fun _ hw ↦ ⟨(hΩ₀ hw).1, hw.2.1⟩
  have hzΩ : ((0 : Euclidean n), z) ∈ Ω :=
    ⟨⟨mem_ball_self T.physicalRadius_pos,
        mem_ball_self T.data.localReference.stateRadius_pos⟩,
      ⟨fun i ↦ (hz i).trans_lt (by linarith [hP.1]), hcol⟩⟩
  have hcontraction : ∀ σ ∈ Ioc (0 : ℝ) 1,
      MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (σ • w.1, w.2)) Ω Ω := by
    intro σ hσ w hw
    have hn : ‖σ • w.1‖ ≤ ‖w.1‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ.1]
      nlinarith [norm_nonneg w.1, hσ.2]
    exact ⟨⟨mem_ball_zero_iff.mpr (hn.trans_lt (mem_ball_zero_iff.mp hw.1.1)),
      mem_ball_zero_iff.mpr (hn.trans_lt (mem_ball_zero_iff.mp hw.1.2))⟩, hw.2⟩
  obtain ⟨ρ, R, hρ, hR, hdouble, hxDouble, hbuffer⟩ :=
    ContinuumRow.NormalizedChartFamily.exists_adapted_double_coefficient_ball T hΩ z hzΩ
  have hsmall : closedBall ((0 : Euclidean n), z) ρ ⊆
      closedBall ((0 : Euclidean n), z) (2 * ρ) := closedBall_subset_closedBall (by linarith)
  have hwork := hsmall.trans hdouble
  have hx := hxDouble.mono_left hsmall
  obtain ⟨η, B, hη, _, hB, hb⟩ := hcoeff row col (0, z) ρ hρ hx (hwork.trans hΩ₀)
  let τ := existenceTime R (liftedLowBound T B) / 4
  have hτ : 0 < τ := div_pos (existenceTime_pos hR (liftedLowBound_nonneg T hB.le)) (by norm_num)
  have hτR16 : τ ≤ R / 16 := by
    have hh := (existenceTime_le hR (liftedLowBound_nonneg T hB.le)).1
    dsimp [τ]
    linarith
  obtain ⟨H, hH, hflow⟩ := exists_uniform_actual_flow_chart T hΩ
    (isCompact_closedBall _ _) hwork hB.le hR hbuffer
  refine ⟨row, col, ρ, R, η, τ, μ * κ, H 1 * (1 + B),
    Ω, B, μ / 2,
    ⟨half_pos hμ, hcontraction, hdouble, hdouble.trans hphysical, hxDouble, ?_⟩,
    hρ, hR, hη, hτ, mul_pos hμ hκ, mul_pos (hH 1) (by linarith), hbuffer, hτR16,
    ⟨hρ, hB, mul_pos hμ hκ, hΩ, hwork,
      hphysical, hx, hbuffer, rfl, hτR16⟩, ?_⟩
  · intro w hw
    have hh := hfrozen w.2 (fun i ↦ ((hdouble hw).2.1 i).le) row col (hdouble hw).2.2
    linarith
  intro C₀ κmet κnormal hκmet hκnormal
  obtain ⟨_A, _hA, hb⟩ := hb C₀ κmet κnormal hκmet hκnormal
  intro F hF hi hrank hlowF hmet hnormal hclose
  obtain ⟨hlow, hk, hl, hd, hc, hnull, hdir, _hhigh⟩ :=
    hb F hF hi hrank hlowF hmet hnormal hclose
  refine ⟨hlow, ?_⟩
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  obtain ⟨D, Φ, Y, _, hD, hsmall, hbig, heq, hΦ, hY, hdomain, hΦD, hYU,
    hΦ₀, hYΦ, hΦY, hcarrier, hYcarrier, hvelocity, hΦbuffer, hYbuffer, hflowHigh⟩ :=
    hflow Q row col (hd.mono hΩ₀) hdir
  have hphys : C ⁻¹' D ⊆ Ω := by
    intro w hw
    have h := hdomain hw
    change C.symm (C w) ∈ Ω at h
    simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using h
  have hY' := hY.mono hbig
  have hsym : ∀ w ∈ Ω, ∀ i, (Q.1 w.1 i).IsSymm := by
    intro w hw i
    have hwU : w.1 ∈ U := hKU (interior_subset (hΩ₀ hw).1.2)
    exact (projectedStress_mem_stressSpace
      ((hF.contDiffAt (hU.mem_nhds hwU)).of_le (by simp)) (hrank w.1 hwU) i).1
  refine ⟨D, Φ, Y,
    ⟨hk.mono hΩ₀, hl.mono hΩ₀, hd.mono hΩ₀, hc.mono hΩ₀, hdir, hsym,
      (fun w hw ↦ hnull w (hΩ₀ hw)), heq, hdomain, hphys,
      hphys.trans hphysical,
      hΦ, hY', hcarrier, hYcarrier, hYbuffer⟩, hD, hsmall, hbig, hphys.trans hphysical,
    hΦ, hY', hΦD, hYU, hΦ₀, hYΦ, hΦY, hcarrier, hYcarrier, hvelocity, hΦbuffer, ?_, ?_⟩
  · have hh := hflowHigh 1
    have hm := mul_le_mul_of_nonneg_left (add_le_add_right hdir 1) (hH 1).le
    linarith [cNorm_nonneg (Icc (-τ) τ ×ˢ
      closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) 1 Y]
  · intro w hw
    exact (hnull w (hΩ₀ (hphys hw))).2.2.2.2.1

/-- The original carrier-data endpoint, projected from the same constructor
with its source-contraction and doubled-minor evidence. Every original witness
and analytic conclusion is retained (`app:ch_waves:thm:leading`). -/
theorem exists_carrier_flow_before_geometry_with_carrier_data {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius) :
    ∃ row col : Fin n, ∃ ρ R η τ g Mc : ℝ,
    ∃ Ωc : Set (Euclidean n × Euclidean 3), ∃ Bc : ℝ,
      0 < ρ ∧ 0 < R ∧ 0 < η ∧ 0 < τ ∧ 0 < g ∧ 0 < Mc ∧
      MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
        (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
        (closedBall ((0 : Euclidean n), z) ρ) ∧ τ ≤ R / 16 ∧
      (0 < ρ ∧ 0 < Bc ∧ 0 < g ∧ IsOpen Ωc ∧
        closedBall ((0 : Euclidean n), z) ρ ⊆ Ωc ∧
        Ωc ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
          parameterInterior (3 * P.radius / 2) ∧
        MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) ρ)
          (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
        MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
          (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
          (closedBall ((0 : Euclidean n), z) ρ) ∧
        τ = existenceTime R (NullTransport.ActualFlow.liftedLowBound T Bc) / 4 ∧
        τ ≤ R / 16) ∧
      ∀ (C₀ κmet κnormal : ℝ), 0 < κmet → 0 < κnormal →
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let e := adaptedCoordinates T.data.adapted
        let C := coordinates (Z := Euclidean 3) e
        let I := Ioo (-τ) τ
        let L := ball ((0 : Euclidean (n - 1)), z) (R / 8)
        ∃ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          (ContDiffOn ℝ ∞ (carrierNullvector T Q col) Ωc ∧
            ContDiffOn ℝ ∞ (carrierConullvector T Q row) Ωc ∧
            ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ωc ∧
            ContDiffOn ℝ ∞ (carrierTransportPotential T Q F row col) Ωc ∧
            cNorm (closedBall ((0 : Euclidean n), z) ρ) 1
              (carrierTransportDirection T Q row col) ≤ Bc ∧
            (∀ w ∈ Ωc, ∀ i, (Q.1 w.1 i).IsSymm) ∧
            (∀ w ∈ Ωc,
              carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
              reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
                (fun j ↦ carrierNullvector T Q col w j) = 0 ∧
              carrierConullvector T Q row w ᵥ*
                reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
              g ≤ |carrierAdaptedDenominator T Q row col w| ∧
              carrierAdaptedDenominator T Q row col w ≠ 0 ∧
              |(carrierAdaptedDenominator T Q row col w)⁻¹| ≤ g⁻¹) ∧
            D = (fun q ↦ (q.1, Φ q)) ''
              (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
            D ⊆ C.symm ⁻¹' Ωc ∧ C ⁻¹' D ⊆ Ωc ∧
            C ⁻¹' D ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
              parameterInterior (3 * P.radius / 2) ∧
            ContDiffOn ℝ ∞ Φ
              (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
            ContDiffOn ℝ ∞ Y D ∧
            (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8),
              ∀ t ∈ Ioo (-τ) τ, (Φ (t, p)).2 = p.2) ∧
            (∀ q ∈ D, (Y q).2 = q.2.2) ∧
            ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ
              ball ((0 : Euclidean (n - 1)), z) (R / 4))) ∧
          IsOpen D ∧
          I ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 32) ⊆ D ∧
          D ⊆ I ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 4) ∧
          C ⁻¹' D ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
            parameterInterior (3 * P.radius / 2) ∧
          ContDiffOn ℝ ∞ Φ (I ×ˢ L) ∧ ContDiffOn ℝ ∞ Y D ∧
          MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ L) D ∧
          MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ L) ∧
          (∀ p ∈ L, Φ (0, p) = p) ∧
          (∀ p ∈ L, ∀ t ∈ I, Y (t, Φ (t, p)) = p) ∧
          (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
          (∀ p ∈ L, ∀ t ∈ I, (Φ (t, p)).2 = p.2) ∧
          (∀ q ∈ D, (Y q).2 = q.2.2) ∧
          (∀ p ∈ L, ∀ t ∈ I, HasDerivAt (fun s ↦ Φ (s, p))
            ((e (carrierTransportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
          ContDiffOn ℝ ∞ Φ
            (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 4)) ∧
          cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) 1 Φ ≤ Mc ∧
          (∀ w ∈ C ⁻¹' D, g ≤ |carrierAdaptedDenominator T Q row col w|) := by
  obtain ⟨row, col, ρ, R, η, τ, g, Mc, Ωc, Bc, _μc, _hsource, hrest⟩ :=
    exists_carrier_flow_before_geometry_with_source_geometry
      (N := N) hn hP T hK hKU hball z hz
  exact ⟨row, col, ρ, R, η, τ, g, Mc, Ωc, Bc, hrest⟩

/-- Original endpoint, projected from the joint carrier-data constructor for
`app:ch_waves:thm:leading`. All witnesses and conclusions are unchanged. -/
theorem exists_carrier_flow_before_geometry {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius) :
    ∃ row col : Fin n, ∃ ρ R η τ g Mc : ℝ,
      0 < ρ ∧ 0 < R ∧ 0 < η ∧ 0 < τ ∧ 0 < g ∧ 0 < Mc ∧
      MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
        (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
        (closedBall ((0 : Euclidean n), z) ρ) ∧ τ ≤ R / 16 ∧
      ∀ (C₀ κmet κnormal : ℝ), 0 < κmet → 0 < κnormal →
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let e := adaptedCoordinates T.data.adapted
        let C := coordinates (Z := Euclidean 3) e
        let I := Ioo (-τ) τ
        let L := ball ((0 : Euclidean (n - 1)), z) (R / 8)
        ∃ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          IsOpen D ∧
          I ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 32) ⊆ D ∧
          D ⊆ I ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 4) ∧
          C ⁻¹' D ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
            parameterInterior (3 * P.radius / 2) ∧
          ContDiffOn ℝ ∞ Φ (I ×ˢ L) ∧ ContDiffOn ℝ ∞ Y D ∧
          MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ L) D ∧
          MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ L) ∧
          (∀ p ∈ L, Φ (0, p) = p) ∧
          (∀ p ∈ L, ∀ t ∈ I, Y (t, Φ (t, p)) = p) ∧
          (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
          (∀ p ∈ L, ∀ t ∈ I, (Φ (t, p)).2 = p.2) ∧
          (∀ q ∈ D, (Y q).2 = q.2.2) ∧
          (∀ p ∈ L, ∀ t ∈ I, HasDerivAt (fun s ↦ Φ (s, p))
            ((e (carrierTransportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
          ContDiffOn ℝ ∞ Φ
            (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 4)) ∧
          cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) 1 Φ ≤ Mc ∧
          (∀ w ∈ C ⁻¹' D, g ≤ |carrierAdaptedDenominator T Q row col w|) := by
  obtain ⟨row, col, ρ, R, η, τ, g, Mc, Ωc, Bc,
    hρ, hR, hη, hτ, hg, hMc, hbuffer, hτR, _hgeometry, hactual⟩ :=
    exists_carrier_flow_before_geometry_with_carrier_data hn hP T hK hKU hball z hz
  refine ⟨row, col, ρ, R, η, τ, g, Mc, hρ, hR, hη, hτ, hg, hMc, hbuffer, hτR, ?_⟩
  intro C₀ κmet κnormal hκmet hκnormal F hF hi hrank hlowF hmet hnormal hclose
  obtain ⟨hlow, D, Φ, Y, _hdata, hrest⟩ :=
    hactual C₀ κmet κnormal hκmet hκnormal F hF hi hrank hlowF hmet hnormal hclose
  exact ⟨hlow, D, Φ, Y, hrest⟩

end JanetCartan.CurrentCoefficientProfiles
