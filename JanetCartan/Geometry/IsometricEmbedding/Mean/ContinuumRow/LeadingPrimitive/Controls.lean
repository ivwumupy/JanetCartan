module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.NormalBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.Detector
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Kernel

/-!
# Primitive controls from the retained full-modulation leading witnesses

This deduction supplies the analytic inputs of the actual continuum row from
`exists_full_joint_leading_wave_before_geometry`. It keeps its scalar, minor,
Hamilton phase and compatible carrier flows. The arbitrary coefficient charts
carry explicit compact and open-region containments; their construction and
common-reference finite covering belong to the parent continuum row.

The detector threshold precedes all source-dependent budgets. The high budget
is exactly the additive reserve-fourteen budget, with constants before the
immersion, initial scalar and high order. Source:
`app:ch_waves:eq:joint-tame`, `app:ch_background:eq:bg-mixed-input`, `bg-T`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.LeadingPrimitive
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open ActualFlow FlowAmplitude ProjectedStressFrame CanonicalCarrier
open LeadingWave.FullModulation ContinuumNormalReduction.TransportSymbol

private theorem controls_enlarge {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {D : PrimitiveNormChart E} {s : ℕ} {M M' B B' H : ℝ} {f : E → G}
    (h : D.Controls s M B H f) (hM : M ≤ M') (hB : B ≤ B') (hH : 0 ≤ H) :
    D.Controls s M' B' H f :=
  ⟨h.smooth, h.low.trans hM, h.high.trans (mul_le_mul_of_nonneg_right hB hH)⟩

/-- Analytic primitive inputs of the continuum row on the SAME retained local
leading witnesses. The full-normal estimate and scalar compatibility premises
are conclusions of `exists_full_joint_leading_wave_before_geometry`; all
carrier Controls, smoothness, measurability and amplitude estimates are derived.
The parent owes precisely the stated geometric containments and fixed masks.
The original carrier measures and square-root frequency weight are preserved
(`app:ch_background:eq:bg-mixed-input`, `bg-T`). -/
theorem exists_primitive_controls_of_jointLeading {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (Kinitial : Set (Euclidean (n - 1) × Euclidean 3))
    (Dc : CoefficientNormCharts n)
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))} (hJ : IsCompact J)
    (hgraph : MapsTo (carrierGraph T) Dc.field.carrier J)
    (hfield : Dc.field.region ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)))
    (hphaseRegion : Dc.field.region ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    (adet : Euclidean n × Euclidean 3) {ρdet : ℝ} (hρdet : 0 < ρdet)
    (hx : MapsTo Prod.fst (closedBall adet ρdet)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hc₀ : closedBall adet ρdet ⊆
      ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius))
    (hLa : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      Dc.field.carrier (closedBall adet ρdet))
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ)
    (hang : ContDiff ℝ ∞ (Function.uncurry angular))
    {Zp : Set CarrierParameter} (hZp : IsCompact Zp)
    (hangular : ∀ z ∉ Zp, ∀ η, angular z η = 0)
    (hsupport : tsupport (FixedCutoffs.physical (n := n) hr 1) ×ˢ Zp ⊆ Dc.field.carrier) :
    ∃ δ > 0,
      ∀ (E : ℕ → ℝ), (∀ j, 0 < E j) →
      ∀ (M₁₅ Mᵣ κmet κ : ℝ), 0 ≤ M₁₅ → 0 ≤ Mᵣ → 0 < κmet → 0 < κ →
      ∃ M > 0, ∃ Cmask ≥ 0, ∃ B : ℕ → ℝ, (∀ j, 1 ≤ B j) ∧
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N), Q.1 = projectedStress F →
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm K 15 F ≤ M₁₅ →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (O : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
        (V : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))),
      IsOpen O → MapsTo Prod.fst O U → O ⊆ domain T → J ⊆ O →
      MapsTo (carrierGraph T) Dc.field.region O →
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) Dc.field.region V →
      ContDiffOn ℝ ∞
        (fun w ↦ scalarAmplitude T Q F row col Φ Y initial w • nullvector T Q col w) O →
      (∀ q ∈ V,
        let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
        scalarAmplitude T Q F row col Φ Y initial
            (w.1, (w.2, T.reference.spatialPatch w.2)) =
          carrierScalarAmplitude T Q F row col φ y initial w) →
      cNorm Kinitial 15 initial ≤ Mᵣ →
      (∀ j, cNorm J j (fullNormal T Q F row col Φ Y initial) ≤
        E j * (1 + cNorm K (j + 14) F + cNorm Kinitial (j + 14) initial)) →
      let e := data T Q F row col φ y initial hr hcell angular FixedCutoffs.highFrequency
      StronglyMeasurable (Function.uncurry (carrierKernel e)) ∧
      (∀ x u, ‖carrierAmplitude e x u‖ ≤ Cmask * Real.sqrt ‖u.2‖) ∧
      ContDiffOn ℝ ∞ (transportPosition T Q) Dc.field.region ∧
      cNorm Dc.field.carrier 3 (transportPosition T Q) ≤ M ∧
      ∀ s, let Hhigh := 1 + cNorm K (s + 14) F + cNorm Kinitial (s + 14) initial
      Dc.Controls s M (B s) Hhigh
        (TransportKernel.coefficientsOfCarrier e (FixedCutoffs.physical hr 1)) ∧
      1 + cNorm Dc.field.carrier (s + 2) (transportPosition T Q) ≤ B s * Hhigh := by
  have hL : IsCompact Dc.field.carrier := isCompact_closedBall ..
  have hparameter : Dc.field.region ⊆ univ ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)) := fun p hp ↦ ⟨mem_univ _, (hfield hp).2⟩
  have hLO : Dc.field.carrier ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)) :=
    fun p hp ↦ ⟨(hfield (Dc.field.ball_subset hp)).1.2, (hfield (Dc.field.ball_subset hp)).2⟩
  obtain ⟨δ, Mq, hδ, hMq, hq⟩ := exists_projected_canonical_quadratic_bounds_before_geometry
    T (N := N) hP adet hρdet hx hc₀ hL hLa hK hKU hball
  refine ⟨δ, hδ, ?_⟩
  intro E hE M₁₅ Mᵣ κmet κ hM₁₅ hMᵣ hκmet hκ
  obtain ⟨Bq, hBq, hq⟩ := hq M₁₅ κmet κ hκmet hκ
  obtain ⟨Mn, hMn, Bn, hBn, hn⟩ := exists_normalField_bounds_of_jointLeading T (N := N)
    hP Dc.field hparameter hJ hgraph K Kinitial E hE hM₁₅ hMᵣ
  obtain ⟨Mp, hMp, Bp, hBp, hp⟩ := exists_projected_transportPosition_primitive_bounds T (N := N)
    hP hL hLO hK hKU hball hM₁₅ hκmet hκ Kinitial
  obtain ⟨Mm, hMm, Bm, hBm, hm⟩ := exists_fixedMask_controls Dc hr angular hang.contDiffOn
  let M := Mn + Mq + Mp + Mm
  have hM : 0 < M := by dsimp [M]; positivity
  let B := fun s ↦ Bm s + (1 + Bn s) + (1 + Bq s) + Bp s
  have hB (s) : 1 ≤ B s := by
    dsimp [B]
    linarith [hBm s, hBn s, hBq s, hBp s]
  let Cmask := cNorm (Zp ×ˢ closedBall (0 : Euclidean (n - 1)) 1) 0 (Function.uncurry angular) *
    Mn ^ 2 * Mq
  have hCmask : 0 ≤ Cmask := mul_nonneg (mul_nonneg (cNorm_nonneg ..) (sq_nonneg _)) hMq.le
  refine ⟨M, hM, Cmask, hCmask, B, hB, ?_⟩
  intro Q F hQ hF hi hrank hFM hmet hnormal hclose row col Φ Y φ y initial O V
    hO hxO hphase hJO hregion hcomp hnull hcompat hrM hfull
  dsimp only
  let e := data T Q F row col φ y initial hr hcell angular FixedCutoffs.highFrequency
  let q := fun p : Euclidean n × CarrierParameter ↦
    quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2))
  obtain ⟨hnreg', hnlow, hnhigh⟩ := hn Q F row col Φ Y φ y initial O V
    hO hxO hphase hJO hregion hcomp hF hi hrank hnull hcompat hFM hrM hfull
  have hqreg : ContDiffOn ℝ ∞ q Dc.field.region :=
    (quadratic_canonical_smooth T hP Q).mono hfield
  have hpred := (transportPosition_smooth T Q hP).mono hphaseRegion
  have hfour : cNorm K 4 F ≤ M₁₅ := (cNorm_mono_order (by omega)).trans hFM
  have hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold := by
    rw [← hQ]
    exact Q.2.2
  have hQeq : (⟨projectedStress F,
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
        {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold}) = Q :=
    Subtype.ext hQ.symm
  have hclose' : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < δ := by
    rw [← hQ]
    exact hclose
  have hqq := hq F hF hi hrank hfour hmet hnormal hclose' hlow
  have hpp := hp F hF hi hrank hFM hmet hnormal hlow
  dsimp only at hqq hpp
  rw [hQeq, ← hQ] at hqq
  rw [hQeq] at hpp
  have hqlow : cNorm Dc.field.carrier 1 q ≤ Mq :=
    (le_add_of_nonneg_right (cNorm_nonneg ..)).trans hqq.1
  have hqrlow : cNorm Dc.field.carrier 1 (fun p ↦ (q p).ofLp) ≤ Mq :=
    (le_add_of_nonneg_left (cNorm_nonneg ..)).trans hqq.1
  refine ⟨?_, ?_, hpred, hpp.1.trans (by dsimp [M]; linarith), ?_⟩
  · exact stronglyMeasurable_carrierKernel_of_local_primitives T Q F row col φ y initial
      hr hcell angular Dc.field.isOpen_region hpred.continuousOn hnreg'.continuousOn
      hqreg.continuousOn hang.continuous hangular (hsupport.trans Dc.field.ball_subset)
  · exact norm_carrierAmplitude_le_of_primitive_norms T Q F row col φ y initial hr hcell angular
      Dc.field hZp hangular hang hsupport hnreg' hqreg hMn.le hMq.le hnlow hqlow
  · intro s
    let W := 1 + cNorm K (s + 14) F +
      cNorm Kinitial (s + 14) initial
    have hW : 1 ≤ W := by
      dsimp [W]
      linarith [cNorm_nonneg K (s + 14) F,
        cNorm_nonneg Kinitial (s + 14) initial]
    have hBnB : 1 + Bn s ≤ B s := by
      dsimp [B]
      linarith [hBm s, hBq s, hBp s]
    have hBqB : 1 + Bq s ≤ B s := by
      dsimp [B]
      linarith [hBm s, hBn s, hBp s]
    have hBpB : Bp s ≤ B s := by
      dsimp [B]
      linarith [hBm s, hBn s, hBq s]
    have hBmB : Bm s ≤ B s := by
      dsimp [B]
      linarith [hBn s, hBq s, hBp s]
    have hnh : 1 + cNorm Dc.field.carrier s
        (Function.uncurry (normalField T Q F row col φ y initial)) ≤ (1 + Bn s) * W := by
      have hh := hnhigh s
      change cNorm Dc.field.carrier s _ ≤ Bn s * W at hh
      nlinarith
    have hqh : cNorm Dc.field.carrier s (fun p ↦ (q p).ofLp) ≤ Bq s * W := by
      have hh := (le_add_of_nonneg_left (cNorm_nonneg Dc.field.carrier s q)).trans (hqq.2 s)
      apply hh.trans
      apply mul_le_mul_of_nonneg_left _ (hBq s).le
      have ho : cNorm K (s + 4) F ≤ cNorm K (s + 14) F := cNorm_mono_order (by omega)
      have h0 := cNorm_nonneg Kinitial (s + 14) initial
      dsimp [W]
      linarith
    obtain ⟨hm₁, hm₂, hm₃⟩ := hm s W hW
    constructor
    · rw [coefficientsOfCarrier_data]
      refine ⟨controls_enlarge hm₁ (by dsimp [M]; linarith) hBmB (by linarith),
        controls_enlarge hm₂ (by dsimp [M]; linarith) hBmB (by linarith),
        controls_enlarge hm₃ (by dsimp [M]; linarith) hBmB (by linarith), ?_, ?_⟩
      · exact ⟨hnreg', hnlow.trans (by dsimp [M]; linarith),
          hnh.trans (mul_le_mul_of_nonneg_right hBnB (by linarith))⟩
      · refine ⟨PiLp.contDiff_ofLp.comp_contDiffOn hqreg,
          hqrlow.trans (by dsimp [M]; linarith), ?_⟩
        have hh : 1 + cNorm Dc.field.carrier s (fun p ↦ (q p).ofLp) ≤ (1 + Bq s) * W := by
          nlinarith
        exact hh.trans (mul_le_mul_of_nonneg_right hBqB (by linarith))
    · exact (hpp.2 initial s).trans (mul_le_mul_of_nonneg_right hBpB (by linarith))

end JanetCartan.ContinuumRow.LeadingPrimitive
