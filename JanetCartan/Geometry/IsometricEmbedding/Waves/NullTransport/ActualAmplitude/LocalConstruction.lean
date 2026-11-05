module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.PositiveBound
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.Buffers
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.UniformFlow
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.CoefficientBounds

/-!
# Actual positive null transport on a buffered local patch

For each point of the original closed carrier cube, choose a fixed minor, a
physical coefficient ball and an adapted state buffer BEFORE the immersion.
The coefficient estimate produces the low direction bound; the actual ODE
construction then supplies the flow and its inverse. The characteristic formula
solves the prescribed positive problem (`app:ch_waves:thm:leading`).

This closes local existence from primitive data. `FiniteConstruction` retains
the finite covering and positivity; `TameConstruction` instantiates the joint
one-high estimate on the same flows and fixed compact working sets.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.NullTransport
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame ActualFlow FlowAmplitude

/-- Construct the actual prescribed positive scalar and its null amplitude
near every point of the original closed carrier cube. The minor, all radii,
positive frame threshold and time interval precede the immersion and initial
scalar. The flow is constructed from the proved coefficient bound, and every
hypothesis of `carrierScalarAmplitude_spec` is discharged. The coefficient
estimates retain one common reserve five and constants chosen before `F`.
The adapted buffer inclusion and time-radius comparison also precede `F`,
so they can be used to choose amplitude tame constants before the immersion.
A positive initial lower bound and a fixed `C⁵` immersion budget give an
explicit lower bound on the whole flow tube. The one-high amplitude estimate
is not asserted here (`app:ch_waves:thm:leading`). -/
theorem exists_projected_local_positive_amplitude {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius) :
    ∃ row col : Fin n, ∃ ρ R η τ g : ℝ, ∃ A H : ℕ → ℝ,
      0 < ρ ∧ 0 < R ∧ 0 < η ∧ 0 < τ ∧ 0 < g ∧ (∀ m, 0 < A m) ∧ (∀ m, 0 < H m) ∧
      MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
        (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
        (closedBall ((0 : Euclidean n), z) ρ) ∧ τ ≤ R / 16 ∧
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
          (∀ w ∈ C ⁻¹' D,
            carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
            carrierConullvector T Q row w ᵥ*
              reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
            carrierAdaptedDenominator T Q row col w ≠ 0) ∧
          (∀ m,
            cNorm (closedBall ((0 : Euclidean n), z) ρ) m (carrierNullvector T Q col) +
            cNorm (closedBall ((0 : Euclidean n), z) ρ) m (carrierConullvector T Q row) +
            cNorm (closedBall ((0 : Euclidean n), z) ρ) m (carrierAdaptedDenominator T Q row col) +
            cNorm (closedBall ((0 : Euclidean n), z) ρ) m
              (fun w ↦ (carrierAdaptedDenominator T Q row col w)⁻¹) +
            cNorm (closedBall ((0 : Euclidean n), z) ρ) m (carrierTransportDirection T Q row col) +
            cNorm (closedBall ((0 : Euclidean n), z) ρ) m (carrierTransportPotential T Q F row col) ≤
              A m * (1 + cNorm K (m + 5) F)) ∧
          (∀ m,
            cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) m Φ +
              cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) m Y ≤
                H m * (1 + cNorm K (m + 5) F)) ∧
          (∀ w ∈ closedBall ((0 : Euclidean n), z) ρ,
            ContDiffAt ℝ ∞ (carrierNullvector T Q col) w ∧
            ContDiffAt ℝ ∞ (carrierTransportDirection T Q row col) w ∧
            ContDiffAt ℝ ∞ (carrierTransportPotential T Q F row col) w) ∧
          ContDiffOn ℝ ∞ Φ
            (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 4)) ∧
          ContDiffOn ℝ ∞ Y
            (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 4)) ∧
          MapsTo C.symm (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
            (closedBall ((0 : Euclidean n), z) ρ) ∧
          τ ≤ R / 16 ∧
          (∀ w ∈ C ⁻¹' D, g ≤ |carrierAdaptedDenominator T Q row col w| ∧
            |(carrierAdaptedDenominator T Q row col w)⁻¹| ≤ g⁻¹) ∧
          ∀ (r : Euclidean (n - 1) × Euclidean 3 → ℝ),
            ContDiffOn ℝ ∞ r L → (∀ p ∈ L, 0 < r p) →
            let α := carrierScalarAmplitude T Q F row col Φ Y r
            ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
              ContDiffOn ℝ ∞ (fun w ↦ α w • carrierNullvector T Q col w) (C ⁻¹' D) ∧
              (∀ p ∈ L, α (T.data.adapted.embedding p.1, p.2) = r p) ∧
              (∀ w ∈ C ⁻¹' D, 0 < α w) ∧
              (∀ K' : Set (Euclidean n × Euclidean 3), IsCompact K' → K' ⊆ C ⁻¹' D →
                ∃ m > 0, ∀ w ∈ K', m ≤ α w) ∧
              (∀ w ∈ C ⁻¹' D,
                fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q row col w) +
                  carrierTransportPotential T Q F row col w * α w = 0) ∧
              (∀ w ∈ C ⁻¹' D,
                reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
                  (fun j ↦ (α w • carrierNullvector T Q col w) j) = 0) ∧
              (∀ w ∈ C ⁻¹' D, carrierConullvector T Q row w ⬝ᵥ reducedOperator F Q.1
                (fun x ↦ α (x, w.2) • carrierNullvector T Q col (x, w.2)) w.1 = 0) ∧
              (∀ m C₅ : ℝ, 0 ≤ m → cNorm K 5 F ≤ C₅ → (∀ p ∈ L, m ≤ r p) →
                ∀ w ∈ C ⁻¹' D, m * Real.exp (-(A 0 * (1 + C₅)) * τ) ≤ α w) := by
  obtain ⟨δ, μ, κ, hδ, hμ, hκ, V, hV, hcover, hcoeff⟩ :=
    exists_projected_coefficient_bounds (N := N) hn hP T hK hKU hball C₀ hκmet hκnormal
  obtain ⟨row, hrow⟩ := mem_iUnion.mp (hcover hz)
  obtain ⟨col, hcol⟩ := mem_iUnion.mp hrow
  let Ω := (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
    (parameterInterior (3 * P.radius / 2) ∩ V row col)
  have hΩ : IsOpen Ω := (isOpen_ball.inter isOpen_interior).prod
    ((isOpen_parameterInterior _).inter (hV row col))
  have h0K : (0 : Euclidean n) ∈ interior K :=
    mem_interior.mpr ⟨ball 0 T.data.localReference.stateRadius,
      ball_subset_closedBall.trans hball, isOpen_ball,
      mem_ball_self T.data.localReference.stateRadius_pos⟩
  have hzΩ : ((0 : Euclidean n), z) ∈ Ω :=
    ⟨⟨mem_ball_self T.physicalRadius_pos, h0K⟩,
      ⟨fun i ↦ (hz i).trans_lt (by linarith [hP.1]), hcol⟩⟩
  obtain ⟨ρ, R, hρ, hR, hwork, hx, hbuffer⟩ := exists_adapted_coefficient_ball T hΩ z hzΩ
  obtain ⟨η, B, A, hη, _, hB, hA, hb⟩ := hcoeff row col (0, z) ρ hρ hx hwork
  let τ := existenceTime R (liftedLowBound T B) / 4
  have hτ : 0 < τ := div_pos (existenceTime_pos hR (liftedLowBound_nonneg T hB.le)) (by norm_num)
  have hτR16 : τ ≤ R / 16 := by
    have hh := (existenceTime_le hR (liftedLowBound_nonneg T hB.le)).1
    dsimp [τ]
    linarith
  obtain ⟨H, hH, hflow⟩ := exists_uniform_actual_flow_chart T hΩ
    (isCompact_closedBall _ _) hwork hB.le hR hbuffer
  refine ⟨row, col, ρ, R, η, τ, μ * κ, A, fun m ↦ H m * (1 + A m),
    hρ, hR, hη, hτ, mul_pos hμ hκ, hA,
    (fun m ↦ mul_pos (hH m) (by have := hA m; linarith)), hbuffer, hτR16, ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hclose
  obtain ⟨hlow, hk, hl, hd, hc, hnull, hdir, hhigh⟩ :=
    hb F hF hi hrank hlowF hmet hnormal hclose
  refine ⟨hlow, ?_⟩
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  obtain ⟨D, Φ, Y, _, hD, hsmall, hbig, _, hΦ, hY, hdomain, hΦD, hYU,
    hΦ₀, hYΦ, hΦY, hcarrier, hYcarrier, hvelocity, hΦbuffer, hYbuffer, hflowHigh⟩ :=
    hflow Q row col hd hdir
  have hphys : C ⁻¹' D ⊆ Ω := by
    intro w hw
    have h := hdomain hw
    change C.symm (C w) ∈ Ω at h
    simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using h
  have hY' := hY.mono hbig
  have hτR : τ ≤ R := by
    have hh := (existenceTime_le hR (liftedLowBound_nonneg T hB.le)).1
    dsimp [τ]
    linarith
  have hballDomain : MapsTo C.symm D (closedBall ((0 : Euclidean n), z) ρ) := by
    intro q hq
    apply hbuffer
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    have hq' := hbig hq
    constructor
    · simpa only [Real.dist_eq, sub_zero] using
        (abs_le.mpr ⟨hq'.1.1.le, hq'.1.2.le⟩).trans hτR
    · exact (mem_ball.mp hq'.2).le.trans (by linarith)
  have hpot0 : cNorm (closedBall ((0 : Euclidean n), z) ρ) 0
      (carrierTransportPotential T Q F row col) ≤ A 0 * (1 + cNorm K 5 F) := by
    have hh := hhigh 0
    norm_num only [zero_add] at hh
    linarith [cNorm_nonneg (closedBall ((0 : Euclidean n), z) ρ) 0 (carrierNullvector T Q col),
      cNorm_nonneg (closedBall ((0 : Euclidean n), z) ρ) 0 (carrierConullvector T Q row),
      cNorm_nonneg (closedBall ((0 : Euclidean n), z) ρ) 0 (carrierAdaptedDenominator T Q row col),
      cNorm_nonneg (closedBall ((0 : Euclidean n), z) ρ) 0
        (fun w ↦ (carrierAdaptedDenominator T Q row col w)⁻¹),
      cNorm_nonneg (closedBall ((0 : Euclidean n), z) ρ) 0 (carrierTransportDirection T Q row col)]
  have hpotBound (w) (hw : w ∈ C ⁻¹' D) :
      |carrierTransportPotential T Q F row col w| ≤ A 0 * (1 + cNorm K 5 F) := by
    have hmem : w ∈ closedBall ((0 : Euclidean n), z) ρ := by
      have hh := hballDomain hw
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      (fun q hq ↦ (hc.contDiffAt (hΩ.mem_nhds (hwork hq))).of_le (show (0 : ℕ∞ω) ≤ ∞ by simp))
      hmem (Nat.zero_le 0)
    have hb' : |carrierTransportPotential T Q F row col w| ≤
        cNorm (closedBall ((0 : Euclidean n), z) ρ) 0
          (carrierTransportPotential T Q F row col) := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hh
    exact hb'.trans hpot0
  refine ⟨D, Φ, Y, hD, hsmall, hbig, (fun w hw ↦ ⟨(hphys hw).1, (hphys hw).2.1⟩),
    hΦ, hY', hΦD, hYU, hΦ₀, hYΦ, hΦY, hcarrier, hYcarrier, hvelocity, ?_, hhigh, ?_, ?_,
    hΦbuffer, hYbuffer, hbuffer, hτR16, ?_, ?_⟩
  · intro w hw
    have hh := hnull w (hphys hw)
    exact ⟨hh.1, hh.2.1, hh.2.2.2.1, hh.2.2.2.2.2.1⟩
  · intro m
    have hh := hhigh m
    have hdirHigh : cNorm (closedBall ((0 : Euclidean n), z) ρ) m
        (carrierTransportDirection T Q row col) ≤ A m * (1 + cNorm K (m + 5) F) := by
      linarith [cNorm_nonneg (closedBall ((0 : Euclidean n), z) ρ) m (carrierNullvector T Q col),
        cNorm_nonneg (closedBall ((0 : Euclidean n), z) ρ) m (carrierConullvector T Q row),
        cNorm_nonneg (closedBall ((0 : Euclidean n), z) ρ) m (carrierAdaptedDenominator T Q row col),
        cNorm_nonneg (closedBall ((0 : Euclidean n), z) ρ) m
          (fun w ↦ (carrierAdaptedDenominator T Q row col w)⁻¹),
        cNorm_nonneg (closedBall ((0 : Euclidean n), z) ρ) m (carrierTransportPotential T Q F row col)]
    apply (hflowHigh m).trans
    have hinner : 1 + cNorm (closedBall ((0 : Euclidean n), z) ρ) m
        (carrierTransportDirection T Q row col) ≤ (1 + A m) * (1 + cNorm K (m + 5) F) := by
      nlinarith [cNorm_nonneg K (m + 5) F]
    exact (mul_le_mul_of_nonneg_left hinner (hH m).le).trans_eq (by ring)
  · intro w hw
    exact ⟨hk.contDiffAt (hΩ.mem_nhds (hwork hw)), hd.contDiffAt (hΩ.mem_nhds (hwork hw)),
      hc.contDiffAt (hΩ.mem_nhds (hwork hw))⟩
  · intro w hw
    have hh := (hnull w (hphys hw)).2.2.2.2
    exact ⟨hh.1, hh.2.2⟩
  · intro r hr hrpos
    have hsym (w) (hw : w ∈ C ⁻¹' D) (i) : (Q.1 w.1 i).IsSymm := by
      have hxU : w.1 ∈ U := hKU (interior_subset (hphys hw).1.2)
      exact (projectedStress_mem_stressSpace
        ((hF.contDiffAt (hU.mem_nhds hxU)).of_le (by simp)) (hrank w.1 hxU) i).1
    obtain ⟨hα, hαk, hinit, hpos, hcompact, hpde, hsymbol, hreduce⟩ :=
      carrierScalarAmplitude_spec T Q F row col isOpen_Ioo ordConnected_Ioo
        isOpen_ball hD ⟨neg_neg_of_pos hτ, hτ⟩ (hk.mono hphys) (hc.mono hphys)
        hsym (fun w hw ↦ (hnull w (hphys hw)).2.2.2.2.2.1)
        (fun w hw ↦ (hnull w (hphys hw)).2.2.1) hr hrpos hΦ hΦD hΦ₀ hY' hYU hYΦ hΦY hvelocity
    refine ⟨hα, hαk, hinit, hpos, hcompact, hpde, hsymbol, hreduce, ?_⟩
    intro m C₅ hm hC₅ hrmin w hw
    have hC₅pos : 0 ≤ C₅ := (cNorm_nonneg K 5 F).trans hC₅
    exact carrierScalarAmplitude_lower_bound T Q F row col hτ
      (mul_nonneg (hA 0).le (by linarith)) hm hΦD hYU
      (fun w hw ↦ (hpotBound w hw).trans
        (mul_le_mul_of_nonneg_left (add_le_add_right hC₅ 1) (hA 0).le)) hrmin hw

end JanetCartan.NullTransport
