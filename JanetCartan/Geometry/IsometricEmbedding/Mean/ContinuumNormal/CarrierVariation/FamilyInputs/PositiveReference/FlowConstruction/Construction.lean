module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart

/-!
# Actual null flows with retained common comparison buffers

Choose the coefficient bound and admissibility threshold on an outer ball.
A later fixed open restriction only shrinks the coefficient and adapted balls;
it does not reduce the threshold or discard an already admissible reference.
The SAME `UniformFlow` maps supply all chart witnesses and the literal scalar.
Consumer: `PositiveReference`, for `app:ch_background:prop:bg-frame` and
`app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow ProjectedStressFrame

/-- Construct common coefficients, a positive radius and the exact ODE time,
then the actual positive-null charts for every admissible immersion. The
threshold and low direction bound precede an arbitrary fixed open restriction
containing the physical/carrier center. Thus restricting to the parent's
Hamilton target does not impose a smaller absolute stress threshold on a
previously admitted reference. All geometric hypotheses of the actual
coefficient producer are retained. Every field of `Chart`, including its low
bound, ODE, inverse identities and scalar problem, is constructed.
Source: `app:ch_waves:thm:leading`, `app:ch_background:prop:bg-frame`. -/
theorem exists_restricted_positive_charts {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKFU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ KF)
    (C₀ : ℝ) {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius) :
    ∃ row col : Fin n, ∃ η M g : ℝ, 0 < η ∧ 0 < M ∧ 0 < g ∧
      ∀ O : Set (Euclidean n × Euclidean 3), IsOpen O → ((0 : Euclidean n), z) ∈ O →
      ∃ Ω : Set (Euclidean n × Euclidean 3), ∃ ρ R τ : ℝ,
        IsOpen Ω ∧ 0 < ρ ∧ 0 < R ∧ 0 < τ ∧
        τ = existenceTime R (liftedLowBound T M) / 4 ∧ τ ≤ R / 16 ∧
        Ω ⊆ O ∧
        Ω ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior KF) ×ˢ
          parameterInterior (3 * P.radius / 2) ∧
        closedBall ((0 : Euclidean n), z) ρ ⊆ Ω ∧
        MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) ρ)
          (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
        MapsTo (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
          (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
          (closedBall ((0 : Euclidean n), z) ρ) ∧
        ∀ (F : Euclidean n → Euclidean N) (_hF : ContDiffOn ℝ ∞ F U)
          (_hi : IsImmersionOn F U) (_hrank : HasFullNormalRankOn F U),
          cNorm KF 4 F ≤ C₀ →
          (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
          (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
            κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
          cNorm KF 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
          ∃ c : Chart T Ω (closedBall ((0 : Euclidean n), z) ρ)
              ((0 : Euclidean (n - 1)), z) R M τ row col F,
            ∀ w ∈ Ω, g ≤ |carrierAdaptedDenominator T c.Q row col w| ∧
              |(carrierAdaptedDenominator T c.Q row col w)⁻¹| ≤ g⁻¹ := by
  obtain ⟨δ, μ, κ, _hδ, hμ, hκ, V, hV, hcover, hcoeff⟩ :=
    exists_projected_coefficient_bounds (N := N) hn hP T hKF hKFU hball C₀ hκmet hκnormal
  obtain ⟨row, hrow⟩ := mem_iUnion.mp (hcover hz)
  obtain ⟨col, hcol⟩ := mem_iUnion.mp hrow
  let Ω₀ := (ball (0 : Euclidean n) T.physicalRadius ∩ interior KF) ×ˢ
    (parameterInterior (3 * P.radius / 2) ∩ V row col)
  have hΩ₀ : IsOpen Ω₀ := (isOpen_ball.inter isOpen_interior).prod
    ((isOpen_parameterInterior _).inter (hV row col))
  have h0K : (0 : Euclidean n) ∈ interior KF :=
    mem_interior.mpr ⟨ball 0 T.data.localReference.stateRadius,
      ball_subset_closedBall.trans hball, isOpen_ball,
      mem_ball_self T.data.localReference.stateRadius_pos⟩
  have hzΩ₀ : ((0 : Euclidean n), z) ∈ Ω₀ :=
    ⟨⟨mem_ball_self T.physicalRadius_pos, h0K⟩,
      ⟨fun i ↦ (hz i).trans_lt (by linarith [hP.1]), hcol⟩⟩
  obtain ⟨ρ₀, R₀, hρ₀, _hR₀, hwork₀, hx₀, _hbuffer₀⟩ :=
    exists_adapted_coefficient_ball T hΩ₀ z hzΩ₀
  obtain ⟨η, M, A, hη, _hηδ, hM, _hA, hb⟩ := hcoeff row col (0, z) ρ₀ hρ₀ hx₀ hwork₀
  refine ⟨row, col, η, M, μ * κ, hη, hM, mul_pos hμ hκ, ?_⟩
  intro O hO hzO
  let Ω := (Ω₀ ∩ O) ∩ ball ((0 : Euclidean n), z) ρ₀
  have hΩ : IsOpen Ω := (hΩ₀.inter hO).inter isOpen_ball
  have hzΩ : ((0 : Euclidean n), z) ∈ Ω := ⟨⟨hzΩ₀, hzO⟩, mem_ball_self hρ₀⟩
  obtain ⟨ρ, R, hρ, hR, hwork, hx, hbuffer⟩ := exists_adapted_coefficient_ball T hΩ z hzΩ
  have houter : closedBall ((0 : Euclidean n), z) ρ ⊆ closedBall ((0 : Euclidean n), z) ρ₀ :=
    fun _ hw ↦ ball_subset_closedBall (hwork hw).2
  let τ := existenceTime R (liftedLowBound T M) / 4
  have hτ : 0 < τ := div_pos (existenceTime_pos hR (liftedLowBound_nonneg T hM.le)) (by norm_num)
  have hτR : τ ≤ R / 16 := by
    have hh := (existenceTime_le hR (liftedLowBound_nonneg T hM.le)).1
    dsimp [τ]
    linarith
  obtain ⟨H, _hH, hflow⟩ := exists_uniform_actual_flow_chart T hΩ
    (isCompact_closedBall _ _) hwork hM.le hR hbuffer
  refine ⟨Ω, ρ, R, τ, hΩ, hρ, hR, hτ, rfl, hτR,
    (fun _ hw ↦ hw.1.2), (fun _ hw ↦ ⟨hw.1.1.1, hw.1.1.2.1⟩), hwork, hx, hbuffer, ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hclose
  obtain ⟨hlow, hk, hl, hd, hc, hnull, hdir, _hhigh⟩ :=
    hb F hF hi hrank hlowF hmet hnormal hclose
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  have hΩΩ₀ : Ω ⊆ Ω₀ := fun _ hw ↦ hw.1.1
  have hd' : ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ω := hd.mono hΩΩ₀
  have hdir' : cNorm (closedBall ((0 : Euclidean n), z) ρ) 1
      (carrierTransportDirection T Q row col) ≤ M :=
    (cNorm_mono_set_of_contDiffAt houter (isCompact_closedBall _ _)
      (fun w hw ↦ (hd.contDiffAt (hΩ₀.mem_nhds (hwork₀ hw))).of_le (by simp))).trans hdir
  obtain ⟨D, Φ, Y, _hτ', hD, hsmall, hbig, heq, hΦ, hY, hdomain, hΦD, hYD,
    hinit, hYΦ, hΦY, hcarrier, hYcarrier, hode, hΦbuffer, hYbuffer, _hflowHigh⟩ :=
    hflow Q row col hd' hdir'
  refine ⟨{
    Q := Q
    frame_eq := rfl
    null_smooth := hk.mono hΩΩ₀
    conull_smooth := hl.mono hΩΩ₀
    direction_smooth := hd'
    potential_smooth := hc.mono hΩΩ₀
    direction_bound := hdir'
    symm := ?_
    null_spec := ?_
    D := D
    forward := Φ
    inverse := Y
    domain_eq := heq
    domain_open := hD
    small_subset := hsmall
    subset_big := hbig
    domain_coefficients := hdomain
    forward_smooth := hΦ
    inverse_smooth := hY.mono hbig
    forward_range := hΦD
    inverse_range := hYD
    initial := hinit
    inverse_forward := hYΦ
    forward_inverse := hΦY
    forward_parameter := hcarrier
    inverse_parameter := hYcarrier
    ode := hode
    forward_buffer_smooth := hΦbuffer
    inverse_buffer_smooth := hYbuffer }, ?_⟩
  · intro w hw i
    have hxU : w.1 ∈ U := hKFU (interior_subset (hΩΩ₀ hw).1.2)
    exact (projectedStress_mem_stressSpace
      ((hF.contDiffAt (hU.mem_nhds hxU)).of_le (by simp)) (hrank w.1 hxU) i).1
  · intro w hw
    have hh := hnull w (hΩΩ₀ hw)
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.2.1⟩
  · intro w hw
    have hh := (hnull w (hΩΩ₀ hw)).2.2.2.2
    exact ⟨hh.1, hh.2.2⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
