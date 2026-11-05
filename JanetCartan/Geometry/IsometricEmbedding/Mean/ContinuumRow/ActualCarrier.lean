module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ActualPrimitive
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FlowConic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement

/-!
# The actual local uncut canonical carrier

This applies the supported conic constructor to the SAME positive transport
and primitive coefficients constructed by `ActualPrimitive`. In particular,
coefficient controls, smoothness on the coefficient domain, and the operator
bound are conclusions. The prescribed initial scalar and immersion have only
their original smoothness, finite norm, frame-neighborhood and geometric-gap
inputs. All masks and constants precede those varying data.

The continuum-row parent still retains finite incidence coverage, common
measurement cutoffs, history/prepared-scalar instantiation, and identification
with the retained full-modulation family. This local construction supplies the
literal extension, adjoint, cutoff limits and reflected normal needed by those
consumers (`app:ch_background:defn:bg-row`, `bg-T`, `bg-realification`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.CanonicalCarrier
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open ActualFlow FlowAmplitude ProjectedStressFrame FullPhaseCharts.ActualComparison
open CanonicalConic ContinuumNormalReduction TransportSymbol TransportKernel
open CarrierNormalRealization Pseudodifferential AmplitudeBound PeriodicLocalL2

/-- Construct the uncut carrier from the actual positive scalar transport and
the canonical supported conic chart. Every primitive coefficient input of the
global normal producer is discharged. The SAME extension has its literal
initial-variable action and adjoint, strong regularized-adjoint limit, and full
reflected matrix normal. The derivative reserve is fourteen; both real
quadratures and the original product measure are retained
(`app:ch_background:eq:bg-T`, `bg-mixed-input`, `bg-full-complex-amplitude`). -/
theorem exists_actual_canonical_carrier {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {M₁₅ Mᵣ κmet κ : ℝ} (hM₁₅ : 0 ≤ M₁₅) (hMᵣ : 0 ≤ Mᵣ)
    (hκmet : 0 < κmet) (hκ : 0 < κ) {cap : ℝ} (hcap : 0 < cap)
    (s : ℕ) (hreserve : 2 * (n + 1) ≤ s) :
    ∃ row col : Fin n, ∃ R τ : ℝ, 0 < R ∧ 0 < τ ∧ τ ≤ R / 16 ∧
    ∃ t > (0 : ℝ), ‖t • k‖ = 1 / 4 ∧
      NormedSpace.normalize (t • k) = NormedSpace.normalize k ∧
      NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)) =
        NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) ∧
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)
    ∃ (r a r' a' : ℝ) (hr : 0 < r) (ha : 0 < a) (hr' : 0 < r') (ha' : 0 < a')
      (hcell' : 4 * a' < 1 / 2) (hηb : ηb ≠ 0),
      6 * a < cap ∧ r' ≤ r ∧ a' ≤ a ∧ a' ≤ r' ∧
    ∃ δ > (0 : ℝ), ∃ C > (0 : ℝ), ∃ Cpdo > (0 : ℝ), ∃ Cmask ≥ (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 15 F ≤ M₁₅ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
      ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      let Ccoord := coordinates (adaptedCoordinates T.data.adapted)
      let p₀ := ((0 : Euclidean (n - 1)), z₀)
      ∃ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
      ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
        IsOpen D ∧ Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D ∧
        D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4) ∧
        (∀ p ∈ ball p₀ (R / 8), Φ (0, p) = p) ∧
        (∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ, Y (t, Φ (t, p)) = p) ∧
        (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧ (∀ q ∈ D, (Y q).2 = q.2.2) ∧
        ∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ,
          ContDiffOn ℝ ∞ initial (ball p₀ (R / 4)) →
          (∀ p ∈ ball p₀ (R / 8), 0 < initial p) →
          cNorm (closedBall p₀ (R / 8)) 15 initial ≤ Mᵣ →
        let α := carrierScalarAmplitude T Q F row col Φ Y initial
        let e := data T Q F row col Φ Y initial ha' hcell'
          (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
          FixedCutoffs.highFrequency
        let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
        let J := symbolJacobian T Q
        let u := symbolInverse T Q z₀ ηb r (6 * a)
        let Ω := symbolDomain T Q z₀ ηb r (6 * a)
        let S := closedBall (spectatorCenter z₀) (a' / 2)
        let H := 1 + cNorm K (s + 14) F +
          cNorm (closedBall p₀ (R / 8)) (s + 14) initial
        ContDiffOn ℝ ∞ α (Ccoord ⁻¹' D) ∧
        (∀ p ∈ ball p₀ (R / 8), α (T.data.adapted.embedding p.1, p.2) = initial p) ∧
        (∀ w ∈ Ccoord ⁻¹' D, 0 < α w) ∧
        (∀ w ∈ Ccoord ⁻¹' D,
          fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q row col w) +
            carrierTransportPotential T Q F row col w * α w = 0) ∧
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
          let eb := data T Q F row col Φ Y initial hb hbcell
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
  obtain ⟨row, col, ρ, R, τ, hρ, hR, hτ, hτR, hbuffer, ε, hε, hprimitive⟩ :=
    exists_actual_canonical_primitive_controls (N := N) hn hP T hK hKU hball z₀
      (fun i ↦ (hz₀ i).le)
  let E := ball (0 : Euclidean n) ε ×ˢ ball (z₀ 0, spectatorCenter z₀) ε
  have hE : IsOpen E := isOpen_ball.prod isOpen_ball
  have hcenter : ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) ∈ E :=
    ⟨mem_ball_self hε, mem_ball_self hε⟩
  obtain ⟨hn', t, ht, htnorm, hdir, hηdir, r, a, r', a', hr, ha, hr', ha',
    hcell', hηb, hacap, houter, hrr, haa, har, Dc, hDcE, hDcOuter, hsupport,
    δc, hδc, hcarrier⟩ :=
    FlowConic.exists_actual_supported_carrier_in_open_of_primitive_controls (N := N)
      T hP hz₀ hk hinc hd hK hKU hball M₁₅ hκmet hκ hcap E hE hcenter
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)
  let angular := angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
  obtain ⟨δp, hδp, M, hM, Cmaskp, hCmaskp, B, hB, hprimitive⟩ :=
    hprimitive Dc hDcE ha' hcell' angular (angularMask_smooth ..)
      (carrierSupport_compact z₀)
      (fun _ hz η ↦ angularMask_zero_outside z₀ (NormedSpace.normalize ηb) ha'
        (angularWidth_spec hηb hr').1 hz η)
      hsupport M₁₅ Mᵣ κmet κ hM₁₅ hMᵣ hκmet hκ
  obtain ⟨Cnorm, hCnorm, Cpdo, hCpdo, Cmask, hCmask, hcarrier⟩ :=
    hcarrier M M (B s) (B s) hM.le hM.le (hB s) (by linarith [hB s]) s hreserve
  refine ⟨row, col, R, τ, hR, hτ, hτR, t, ht, htnorm, hdir, hηdir,
    r, a, r', a', hr, ha, hr', ha', hcell', hηb, hacap, hrr, haa, har,
    min δp δc, lt_min hδp hδc, Cnorm, hCnorm, Cpdo, hCpdo, Cmask, hCmask, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  obtain ⟨hlow, D, Φ, Y, hD, hsmall, hbig, hΦ₀, hYΦ, hΦY, hYcarrier, hscalar⟩ :=
    hprimitive F hF hi hrank hFM hmet hnormal (hclose.trans_le (min_le_left _ _))
  refine ⟨hlow, D, Φ, Y, hD, hsmall, hbig, hΦ₀, hYΦ, hΦY, hYcarrier, ?_⟩
  intro initial hinitial hpositive hinitialBound
  obtain ⟨hα, hα₀, hαpos, htransport, hν, hdet, _, _, _, hYlow, hcontrols⟩ :=
    hscalar initial hinitial hpositive hinitialBound
  refine ⟨hα, hα₀, hαpos, htransport, ?_⟩
  have hsmallNorm : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) ≤
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) :=
    cNorm_mono_set_of_contDiffAt hball hK (fun x hx ↦
      (((contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)).contDiffAt
        (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp))
  obtain ⟨hsupport, Lmask, hLmask, Mmask, hMmask, hmask, hfinite, htestBound,
    hb, hA, V, hV, hVadj, hVtest, hVsupp, hVunique, hVliteral, hVlimit, hVnormal⟩ :=
    hcarrier F hF hi hrank ((cNorm_mono_order (by omega)).trans hFM)
    hmet hnormal hlow (hsmallNorm.trans_lt (hclose.trans_le (min_le_right _ _)))
    row col Φ Y initial hν hdet
    (1 + cNorm K (s + 14) F + cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8))
      (s + 14) initial)
    (by linarith [cNorm_nonneg K (s + 14) F,
      cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (s + 14) initial])
    hYlow (hcontrols s).2 (hcontrols s).1
  refine ⟨hsupport, Lmask, hLmask, Mmask, hMmask, hmask, hfinite, htestBound,
    hb, hA, V, hV, hVadj, hVtest, hVsupp, hVunique, hVliteral, hVlimit, hVnormal, ?_⟩
  intro b hb hbcell hba
  obtain ⟨hVb, hVbtest, hVbadj, hVbsupp, _⟩ :=
    CommonMeasurement.fixed_common_restriction _ hb ha' hbcell hcell' hba
      rfl (fun _ _ ↦ rfl) rfl V hVtest hVliteral _ hVnormal
  exact ⟨hVb.trans hV, hVbtest, hVbadj, hVbsupp,
    CommonMeasurement.carrierChannel_restrictCarrier_normal _ V⟩

end JanetCartan.ContinuumRow.CanonicalCarrier
