module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingCarrier.Buffers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.Controls
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.UniformConic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement

/-!
# Uncut carriers from the actual full-modulation leading family

The scalar, minor and both compatible flows come from the SAME local leading
construction. The supported conic domains, masks and frame tolerance precede
geometric and scalar budgets. Primitive controls and coefficient smoothness
are proved from that leading construction, then the supported global carrier
producer constructs the actual extension, adjoint and full reflected normal.
Sources: `app:ch_background:defn:bg-row`, `bg-T`, `bg-realification`,
`app:ch_waves:eq:joint-tame`, and v2 `new:sec:order-of-choices`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.LeadingCarrier
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ProjectedStressFrame FullPhaseCharts.ActualComparison CanonicalCarrier
open CanonicalConic ContinuumNormalReduction TransportSymbol TransportKernel
open CarrierNormalRealization Pseudodifferential AmplitudeBound PeriodicLocalL2
open LeadingWave LeadingWave.FullModulation LeadingPrimitive CurrentCoefficientProfiles

private theorem normal_summand_le {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (he : 0 ≤ e) :
    c ≤ a + b + c + d + e := by linarith

/-- Actual local leading carrier, with all fixed domains and frame tolerances
chosen before source-dependent budgets. The SAME full-modulation scalar and
normal restrict to the literal carrier integrand. The supported operator
producer's primitive and smoothness hypotheses are discharged; the original
half-order weight, product measure, both quadratures and full reflected normal
are retained. Finite coverage and initialized-history inputs remain with the
finite-row assembly (`app:ch_background:defn:bg-row`, `bg-T`). -/
theorem exists_actual_leading_carrier_before_geometry {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ row col : Fin n, ∃ R σ ε : ℝ, 0 < R ∧ 0 < σ ∧ 0 < ε ∧
    ∃ t > (0 : ℝ), ‖t • k‖ = 1 / 4 ∧
      NormedSpace.normalize (t • k) = NormedSpace.normalize k ∧
      NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)) =
        NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) ∧
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)
    let E := ball (0 : Euclidean n) ε ×ˢ ball (z₀ 0, spectatorCenter z₀) ε
    ∃ (r a r' a' : ℝ) (hr : 0 < r) (ha : 0 < a) (hr' : 0 < r') (ha' : 0 < a')
      (hcell' : 4 * a' < 1 / 2) (hηb : ηb ≠ 0),
      6 * a < cap ∧ coefficientDomain z₀ r (6 * a) ⊆ E ∧
      r' ≤ r ∧ a' ≤ a ∧ a' ≤ r' ∧
    ∃ δ > (0 : ℝ),
    ∀ (MF Mr κmet κ m : ℝ), 0 ≤ MF → 0 ≤ Mr → 0 < κmet → 0 < κ → 0 < m →
    ∃ g cν : ℝ, ∃ Bfull : ℕ → ℝ, 0 < g ∧ 0 < cν ∧ (∀ j, 0 < Bfull j) ∧
    ∀ (s : ℕ) (hreserve : 2 * (n + 1) ≤ s),
    ∃ C > (0 : ℝ), ∃ Cpdo > (0 : ℝ), ∃ Cmask ≥ (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 15 F ≤ MF →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
      ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      let pc := ((0 : Euclidean (n - 1)), z₀)
      let ac := ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀))
      ∃ φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
      ∃ Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
        Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)),
        (∀ initial p, p ∈ E →
          scalarAmplitude T Q F row col Φ Y initial (carrierGraph T p) =
            carrierScalarAmplitude T Q F row col φ y initial (p.1, parameter p.2)) ∧
        ∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ,
          ContDiffOn ℝ ∞ initial (ball pc (R / 4)) →
          cNorm (closedBall pc (R / 8)) 15 initial ≤ Mr →
          (∀ p ∈ ball pc (R / 8), m ≤ initial p) →
        let α := scalarAmplitude T Q F row col Φ Y initial
        let e := data T Q F row col φ y initial ha' hcell'
          (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
          FixedCutoffs.highFrequency
        let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
        let J := symbolJacobian T Q
        let u := symbolInverse T Q z₀ ηb r (6 * a)
        let Ω := symbolDomain T Q z₀ ηb r (6 * a)
        let S := closedBall (spectatorCenter z₀) (a' / 2)
        let H := 1 + cNorm K (s + 14) F + cNorm (closedBall pc (R / 8)) (s + 14) initial
        ContDiffOn ℝ ∞ α (ball ac (2 * σ)) ∧
        (∀ w ∈ closedBall ac (2 * σ), g ≤ α w ∧
          cν ≤ ‖fullNormal T Q F row col Φ Y initial w‖) ∧
        (∀ j, cNorm (closedBall ac σ) j (fullNormal T Q F row col Φ Y initial) ≤
          Bfull j * (1 + cNorm K (j + 14) F + cNorm (closedBall pc (R / 8)) (j + 14) initial)) ∧
        (∀ p ∈ E, normalField T Q F row col φ y initial p.1 p.2 =
          fullNormal T Q F row col Φ Y initial (carrierGraph T p)) ∧
      ∃ hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a',
      ∃ Lmask > 0, ∃ Mmask ≥ 0,
      ∃ hmask : ∀ (Q : ℝ), 1 ≤ Q → CarrierRegularization.MaskHypotheses e
        (parameterTruncatedMask (carrierSupport z₀ (r := a'))
          (radialCarrierMask FixedCutoffs.radialRegularization Q))
        (carrierSupport z₀ (r := a')) (Lmask * Q) Mmask Cmask,
        (∀ (Q : ℝ) (hQ : 1 ≤ Q),
          ‖(hmask Q hQ).operator.comp (hmask Q hQ).operator.adjoint‖ ≤
              (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H)) ∧
          ‖(realQuadratureChannel (hmask Q hQ).operator).comp
              (realQuadratureChannel (hmask Q hQ).operator).adjoint‖ ≤
              (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H))) ∧
        (∀ v : carrierInitialTestSpace n,
          MemLp (carrierTestIntegral e v.val) 2 volume ∧
          (eLpNorm (carrierTestIntegral e v.val) 2 volume).toReal ≤
            Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H))) *
              ‖carrierInitialTestToLp v‖) ∧
      ∃ (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude d J u Ω S)))
        (hA : ∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ fullReflectedMatrixAmplitude d J u Ω S ξ z i j) s (Cpdo * H)),
      ∃ V : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        ‖V‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H))) ∧
        ‖V.adjoint‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H))) ∧
        (∀ v : carrierInitialTestSpace n,
          V (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) ∧
        (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → V f x = 0) ∧
        (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ v : carrierInitialTestSpace n,
            W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) → W = V) ∧
        (∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
          V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) ∧
        (∀ w : ComplexOutputL2 n,
          Filter.Tendsto (fun k : ℕ ↦
            (hmask ((k : ℝ) + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k))).operator.adjoint w)
            Filter.atTop (nhds (V.adjoint w))) ∧
        (realQuadratureChannel V).comp (realQuadratureChannel V).adjoint =
          realOutputCompression (transferOperator
            (vectorTwoPositionL2Operator (by omega) (4 * a')
              (fullReflectedMatrixAmplitude d J u Ω S) hb
              (fullReflectedMatrixAmplitude_supportedInCenteredBox
                d J u Ω S (4 * a') hsupport)
              (Cpdo * H) (fun i j ξ is his ↦ hA i j ξ is (his.trans hreserve)))) ∧
        ∀ {b : ℝ} (hb : 0 < b) (hbcell : 4 * b < 1 / 2), 6 * b < a' →
          let χ := FixedCutoffs.periodic (n := n) hb hbcell 1
          let Vb := CommonMeasurement.restrictCarrier χ V
          let eb := data T Q F row col φ y initial hb hbcell
            (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
            FixedCutoffs.highFrequency
          ‖Vb‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H))) ∧
          (∀ v : carrierInitialTestSpace n,
            Vb (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral eb v.val) ∧
          (∀ w : ComplexOutputL2 n,
            MemLp (carrierAdjointIntegral eb w) 2 (carrierMeasure n) ∧
            Vb.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral eb w) ∧
          (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ eb.outputChart → Vb f x = 0) ∧
          carrierChannel Vb ∘L (carrierChannel Vb).adjoint =
            cutoffMultiplier χ ∘L
              (carrierChannel V ∘L (carrierChannel V).adjoint) ∘L cutoffMultiplier χ := by
  obtain ⟨row, col, ρ, R, η, τ, b, Rc, τc, Mc, rcomp, δcomp, σ,
    hρ, hR, hη, hτ, hb, hRc, hτc, hMc, hrcomp, hδcomp, hσ,
    hτR, hdom, hx, hbuffer, hactual⟩ :=
    exists_full_joint_leading_wave_before_geometry hn hP T hK hKU hball z₀
      (fun i ↦ (hz₀ i).le)
  obtain ⟨ε, hε, ρdet, hρdet, hgraph, hcompE, hfield, hphase, hxdet, hdet, hmaps⟩ :=
    exists_leading_carrier_buffers hP T hKU hball z₀ (fun i ↦ (hz₀ i).le)
      hσ hrcomp hδcomp
  let E := ball (0 : Euclidean n) ε ×ˢ ball (z₀ 0, spectatorCenter z₀) ε
  have hE : IsOpen E := isOpen_ball.prod isOpen_ball
  have hcenter : ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) ∈ E :=
    ⟨mem_ball_self hε, mem_ball_self hε⟩
  have hc := UniformConic.exists_actual_supported_carrier_in_open_before_geometry_of_primitive_controls
      (N := embeddingDimension n) T hP hz₀ hk hinc hd hK hKU hball hcap E hE hcenter
  obtain ⟨hn', hc⟩ := hc
  obtain ⟨t, ht, htnorm, hdir, hηdir, hc⟩ := hc
  obtain ⟨r, a, r', a', hc⟩ := hc
  obtain ⟨hr, ha, hr', ha', hcell', hηb, hc⟩ := hc
  obtain ⟨hacap, houter, hrr, haa, har, hc⟩ := hc
  obtain ⟨Dc, hDcE, hDcOuter, hsupport, δc, hδc, hcarrier⟩ := hc
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)
  let angular := angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
  obtain ⟨δp, hδp, hcontrols⟩ := exists_primitive_controls_of_jointLeading T
    (N := embeddingDimension n) hP hK hKU hball
    (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) Dc (isCompact_closedBall _ _)
    (fun p hp ↦ ball_subset_closedBall (hgraph (hDcE (Dc.field.ball_subset hp))))
    (hDcE.trans hfield) (hDcE.trans hphase) (0, z₀) hρdet hxdet hdet
    (fun p hp ↦ hmaps (hDcE (Dc.field.ball_subset hp))) ha' hcell' angular
    (angularMask_smooth ..) (carrierSupport_compact z₀)
    (fun _ hz η ↦ angularMask_zero_outside z₀ (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 hz η) hsupport
  refine ⟨row, col, R, σ, ε, hR, hσ, hε, ?_⟩
  refine ⟨t, ht, htnorm, hdir, hηdir, ?_⟩
  refine ⟨r, a, r', a', hr, ha, hr', ha', hcell', hηb, ?_⟩
  refine ⟨hacap, houter, hrr, haa, har, min η (min δp δc), lt_min hη (lt_min hδp hδc), ?_⟩
  intro MF Mr κmet κ m hMF hMr hκmet hκ hm
  obtain ⟨g, cν, A, Hflow, Bamp, Bfull, hg, hcν, hA, hHflow, hBamp, hBfull, hactual⟩ :=
    hactual MF Mr κmet κ m hMF hMr hκmet hκ hm
  obtain ⟨M, hM, Cmaskp, hCmaskp, B, hB, hcontrols⟩ :=
    hcontrols Bfull hBfull MF Mr κmet κ hMF hMr hκmet hκ
  refine ⟨g, cν, Bfull, hg, hcν, hBfull, ?_⟩
  intro s hreserve
  obtain ⟨Cnorm, hCnorm, Cpdo, hCpdo, Cmask, hCmask, hcarrier⟩ :=
    hcarrier MF κmet κ hκmet hκ M M (B s) (B s) hM.le hM.le
      (hB s) (by linarith [hB s]) s hreserve
  refine ⟨Cnorm, hCnorm, Cpdo, hCpdo, Cmask, hCmask, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  obtain ⟨hlow, Dcarrier, φ, y, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
    hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcover, hbig, hphys, hballD, hphaseInitial,
    hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
    hΦbuffer, hYbuffer, hflow, hgaps, hcoeff, hcompat, hsolution⟩ :=
    hactual F hF hi hrank ((cNorm_mono_order (by omega)).trans hFM) hmet hnormal
      (hclose.trans_le (min_le_left _ _))
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  let Cfull := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
    (adaptedCoordinates T.data.adapted)
  let O := Cfull ⁻¹' D
  have hO : IsOpen O := hD.preimage Cfull.continuous
  have hOU : MapsTo Prod.fst O U := fun w hw ↦
    hKU (interior_subset (hx (ball_subset_closedBall (hphys hw))).2.2)
  have hOphase : O ⊆ domain T := fun w hw ↦ hdom (ball_subset_closedBall (hphys hw))
  have hJO : closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) σ ⊆ O :=
    (closedBall_subset_closedBall (by linarith)).trans hballD
  have hgraphO : MapsTo (carrierGraph T) E O := fun p hp ↦ hJO (ball_subset_closedBall (hgraph hp))
  have hcomp (initial) (q) (hq : q ∈ Ioo (-δcomp) δcomp ×ˢ
      ball ((0 : Euclidean (n - 1)), z₀) rcomp) := (hcompat q hq).2.2.2.2 initial |>.1
  have hsmallNorm : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) ≤ cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) :=
    cNorm_mono_set_of_contDiffAt hball hK (fun x hx ↦
      ((Q.2.1.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp))
  refine ⟨hlow, φ, y, Φ, Y, ?_, ?_⟩
  · intro initial p hp
    have hh := hcomp initial _ (hcompE hp)
    dsimp only at hh
    rw [ContinuousLinearEquiv.symm_apply_apply] at hh
    exact hh
  intro initial hinitial hrM hrmin
  obtain ⟨hα, hnull, hinit, hpos, hpde, hsymbol, hreduce, habound, hidentity, hjoint⟩ :=
    hsolution initial hinitial ((cNorm_mono_order (by omega)).trans hrM) hrmin
  have hfull (j) : cNorm (closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) σ)
      j (fullNormal T Q F row col Φ Y initial) ≤
      Bfull j * (1 + cNorm K (j + 14) F +
        cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) initial) := by
    apply le_trans _ (hjoint j)
    exact normal_summand_le (cNorm_nonneg ..) (cNorm_nonneg ..)
      (cNorm_nonneg ..) (cNorm_nonneg ..)
  have hnormalEq (p) (hp : p ∈ E) :=
    normalField_eq_fullNormal_on_graph T Q F row col Φ Y φ y initial (hcomp initial) (hcompE hp)
  have hν : ContDiffOn ℝ ∞ (Function.uncurry (normalField T Q F row col φ y initial)) E :=
    ((fullNormal_smooth T Q F row col Φ Y initial hO hOU hOphase hF hi hrank hnull).comp
      ((carrierGraph_smooth T hP).mono (fun p hp ↦ ⟨mem_univ _, (hfield hp).2⟩))
      hgraphO).congr (fun p hp ↦ hnormalEq p hp)
  have hdetreg (i : Fin n) : ContDiffOn ℝ ∞
      (fun p : Euclidean n × CarrierParameter ↦
        quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2)) i) E :=
    contDiffOn_pi.mp (PiLp.contDiff_ofLp.comp_contDiffOn
      ((quadratic_canonical_smooth T hP Q).mono hfield)) i
  obtain ⟨_, _, _, hYlow, hctrl⟩ := hcontrols Q F rfl hF hi hrank hFM hmet hnormal
    (hsmallNorm.trans_lt (hclose.trans_le ((min_le_right _ _).trans (min_le_left _ _))))
    row col Φ Y φ y initial O
    (Ioo (-δcomp) δcomp ×ˢ ball ((0 : Euclidean (n - 1)), z₀) rcomp)
    hO hOU hOphase hJO (fun p hp ↦ hgraphO (hDcE hp)) (fun p hp ↦ hcompE (hDcE hp))
    hnull (hcomp initial) hrM hfull
  refine ⟨hα.mono (ball_subset_closedBall.trans hballD),
    fun w hw ↦ ⟨(hpos w (hballD hw)).1, (hidentity w (hballD hw)).1⟩,
    hfull, hnormalEq, ?_⟩
  have hop := hcarrier F hF hi hrank ((cNorm_mono_order (by omega)).trans hFM)
    hmet hnormal hlow
    (hsmallNorm.trans_lt (hclose.trans_le ((min_le_right _ _).trans (min_le_right _ _))))
    row col φ y initial hν hdetreg
    (1 + cNorm K (s + 14) F + cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8))
      (s + 14) initial)
    (by linarith [cNorm_nonneg K (s + 14) F,
      cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (s + 14) initial])
    hYlow (hctrl s).2 (hctrl s).1
  obtain ⟨hsupport, Lmask, hLmask, Mmask, hMmask, hmask, hop⟩ := hop
  obtain ⟨hfinite, htestBound, hb, hA, V, hop⟩ := hop
  obtain ⟨hV, hVadj, hVtest, hVsupp, hVunique, hVliteral, hVlimit, hVnormal⟩ := hop
  refine ⟨hsupport, Lmask, hLmask, Mmask, hMmask, hmask, hfinite, htestBound,
    hb, hA, V, hV, hVadj, hVtest, hVsupp, hVunique, hVliteral, hVlimit, hVnormal, ?_⟩
  intro b hb hbcell hba
  obtain ⟨hVb, hVbtest, hVbadj, hVbsupp, _⟩ :=
    CommonMeasurement.fixed_common_restriction _ hb ha' hbcell hcell' hba
      rfl (fun _ _ ↦ rfl) rfl V hVtest hVliteral _ hVnormal
  exact ⟨hVb.trans hV, hVbtest, hVbadj, hVbsupp,
    CommonMeasurement.carrierChannel_restrictCarrier_normal _ V⟩

end JanetCartan.ContinuumRow.LeadingCarrier
