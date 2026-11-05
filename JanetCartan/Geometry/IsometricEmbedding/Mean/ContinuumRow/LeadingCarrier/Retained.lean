module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingCarrier.Construction

/-!
# Supported carriers inside retained leading cells

The incidence root need not be the center of a retained leading cell. This
construction places the conic charts inside that cell and uses its existing
minor, full and carrier flows and initial scalar. Its analytic premises are
exact outputs of `exists_finite_retained_leading_family_before_geometry` and
its history version; no carrier controls or operator conclusions are inputs.
The final finite row must instantiate those outputs on one initialized family.

Sources: `app:ch_background:defn:bg-row`, `bg-T`, `bg-realification`,
`app:ch_waves:eq:joint-tame`, and v2 `new:sec:order-of-choices`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.LeadingCarrier
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ProjectedStressFrame FullPhaseCharts.ActualComparison CanonicalCarrier
open CanonicalConic ContinuumNormalReduction TransportSymbol TransportKernel
open CarrierNormalRealization Pseudodifferential AmplitudeBound PeriodicLocalL2
open LeadingWave LeadingWave.FullModulation LeadingPrimitive

/-- Construct the literal uncut carrier inside a previously retained leading
cell, using its SAME supplied scalar, minor and compatible flows. The incidence
center may differ from the leading-cell center. All masks, charts and frame
tolerances precede the geometric and full-normal budgets. The latter bound and
compatibility are proved by `RetainedCover.Finite` and `RetainedCover.History`;
this theorem derives the primitive controls and applies the supported-shell
operator constructor (`app:ch_background:defn:bg-row`, `bg-T`). -/
theorem exists_carrier_in_retained_leading_cell_before_geometry {n N : ℕ}
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (Kinitial : Set (Euclidean (n - 1) × Euclidean 3))
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))} (hJ : IsCompact J)
    (E : Set (Euclidean n × CarrierParameter)) (hE : IsOpen E)
    (hgraph : MapsTo (carrierGraph T) E J)
    (hfield : E ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)))
    (hphase : E ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    (adet : Euclidean n × Euclidean 3) {ρdet : ℝ} (hρdet : 0 < ρdet)
    (hxdet : MapsTo Prod.fst (closedBall adet ρdet)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hdet : closedBall adet ρdet ⊆
      ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius))
    (hmaps : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      E (closedBall adet ρdet))
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    (hcenter : ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) ∈ E)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ t > (0 : ℝ), ‖t • k‖ = 1 / 4 ∧
      NormedSpace.normalize (t • k) = NormedSpace.normalize k ∧
      NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)) =
        NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) ∧
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)
    ∃ (r a r' a' : ℝ) (hr : 0 < r) (ha : 0 < a) (hr' : 0 < r') (ha' : 0 < a')
      (hcell' : 4 * a' < 1 / 2) (hηb : ηb ≠ 0),
      6 * a < cap ∧ coefficientDomain z₀ r (6 * a) ⊆ E ∧
      r' ≤ r ∧ a' ≤ a ∧ a' ≤ r' ∧
    ∃ δ > (0 : ℝ),
    ∀ (Bfull : ℕ → ℝ), (∀ j, 0 < Bfull j) →
    ∀ (MF Mr κmet κ : ℝ), 0 ≤ MF → 0 ≤ Mr → 0 < κmet → 0 < κ →
    ∀ (s : ℕ) (hreserve : 2 * (n + 1) ≤ s),
    ∃ C > (0 : ℝ), ∃ Cpdo > (0 : ℝ), ∃ Cmask ≥ (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 15 F ≤ MF →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin n)
        (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (O : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
        (Vcomp : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))),
      IsOpen O → MapsTo Prod.fst O U → O ⊆ domain T → J ⊆ O →
      MapsTo (carrierGraph T) E O →
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) E Vcomp →
      ContDiffOn ℝ ∞
        (fun w ↦ scalarAmplitude T Q F row col Φ Y initial w • nullvector T Q col w) O →
      (∀ q ∈ Vcomp,
        let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
        scalarAmplitude T Q F row col Φ Y initial
            (w.1, (w.2, T.reference.spatialPatch w.2)) =
          carrierScalarAmplitude T Q F row col φ y initial w) →
      cNorm Kinitial 15 initial ≤ Mr →
      (∀ j, cNorm J j (fullNormal T Q F row col Φ Y initial) ≤
        Bfull j * (1 + cNorm K (j + 14) F + cNorm Kinitial (j + 14) initial)) →
      let e := data T Q F row col φ y initial ha' hcell'
        (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
        FixedCutoffs.highFrequency
      let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
      let J := symbolJacobian T Q
      let u := symbolInverse T Q z₀ ηb r (6 * a)
      let Ω := symbolDomain T Q z₀ ηb r (6 * a)
      let S := closedBall (spectatorCenter z₀) (a' / 2)
      let H := 1 + cNorm K (s + 14) F + cNorm Kinitial (s + 14) initial
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
            (vectorTwoPositionL2Operator (by have := row.isLt; omega) (4 * a')
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
  have hc := UniformConic.exists_actual_supported_carrier_in_open_before_geometry_of_primitive_controls
      (N := N) T hP hz₀ hk hinc hd hK hKU hball hcap E hE hcenter
  obtain ⟨hn, t, ht, htnorm, hdir, hηdir, r, a, r', a', hr, ha, hr', ha',
    hcell', hηb, hacap, houter, hrr, haa, har,
    Dc, hDcE, hDcOuter, hsupport, δc, hδc, hcarrier⟩ := hc
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)
  let angular := angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
  obtain ⟨δp, hδp, hcontrols⟩ := exists_primitive_controls_of_jointLeading T
    (N := N) hP hK hKU hball Kinitial Dc hJ
    (fun p hp ↦ hgraph (hDcE (Dc.field.ball_subset hp)))
    (hDcE.trans hfield) (hDcE.trans hphase) adet hρdet hxdet hdet
    (fun p hp ↦ hmaps (hDcE (Dc.field.ball_subset hp))) ha' hcell' angular
    (angularMask_smooth ..) (carrierSupport_compact z₀)
    (fun _ hz η ↦ angularMask_zero_outside z₀ (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 hz η) hsupport
  refine ⟨t, ht, htnorm, hdir, hηdir, r, a, r', a', hr, ha, hr', ha', hcell', hηb,
    hacap, houter, hrr, haa, har, min δp δc, lt_min hδp hδc, ?_⟩
  intro Bfull hBfull MF Mr κmet κ hMF hMr hκmet hκ s hreserve
  obtain ⟨M, hM, Cmaskp, hCmaskp, B, hB, hcontrols⟩ :=
    hcontrols Bfull hBfull MF Mr κmet κ hMF hMr hκmet hκ
  obtain ⟨Cnorm, hCnorm, Cpdo, hCpdo, Cmask, hCmask, hcarrier⟩ :=
    hcarrier MF κmet κ hκmet hκ M M (B s) (B s) hM.le hM.le
      (hB s) (by linarith [hB s]) s hreserve
  refine ⟨Cnorm, hCnorm, Cpdo, hCpdo, Cmask, hCmask, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose hlow
  dsimp only
  intro row col φ y Φ Y initial
    O Vcomp hO hOU hOphase hJO hgraphO hcompE hnull hcomp hrM hfull
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  have hsmallNorm : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) ≤ cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) :=
    cNorm_mono_set_of_contDiffAt hball hK (fun x hx ↦
      ((Q.2.1.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp))
  have hnormalEq (p) (hp : p ∈ E) :=
    normalField_eq_fullNormal_on_graph T Q F row col Φ Y φ y initial hcomp (hcompE hp)
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
    (hsmallNorm.trans_lt (hclose.trans_le (min_le_left _ _)))
    row col Φ Y φ y initial O Vcomp hO hOU hOphase hJO
    (fun p hp ↦ hgraphO (hDcE hp)) (fun p hp ↦ hcompE (hDcE hp))
    hnull hcomp hrM hfull
  refine ⟨hnormalEq, ?_⟩
  have hop := hcarrier F hF hi hrank ((cNorm_mono_order (by omega)).trans hFM)
    hmet hnormal hlow (hsmallNorm.trans_lt (hclose.trans_le (min_le_right _ _)))
    row col φ y initial hν hdetreg
    (1 + cNorm K (s + 14) F + cNorm Kinitial (s + 14) initial)
    (by linarith [cNorm_nonneg K (s + 14) F, cNorm_nonneg Kinitial (s + 14) initial])
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
