module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.NormalField
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Detector
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Kernel

/-!
# Primitive controls for the SAME canonical carrier

This assembles the five original coefficient norms and the finite-kernel
premises of `exists_carrierL2Extension_globalNormal_of_primitiveNorms`.
All analytic estimates are derived from primitive immersion/initial-data
budgets and the exact retained local-flow outputs. Only fixed domains,
mask supports and their buffer containments are supplied separately by the
conic construction. The high budget is additive with reserve fourteen,
including the geometry order `s + 2`.

Source: `app:ch_background:eq:bg-mixed-input`, `bg-T`,
`bg-full-complex-amplitude`, and `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.CanonicalCarrier
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open ActualFlow FlowAmplitude ProjectedStressFrame
open ContinuumNormalReduction.TransportSymbol

private theorem controls_enlarge {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {D : PrimitiveNormChart E} {s : ℕ} {M M' B B' H : ℝ} {f : E → G}
    (h : D.Controls s M B H f) (hM : M ≤ M') (hB : B ≤ B') (hH : 0 ≤ H) :
    D.Controls s M' B' H f :=
  ⟨h.smooth, h.low.trans hM, h.high.trans (mul_le_mul_of_nonneg_right hB hH)⟩

/-- The literal canonical carrier satisfies the existing five-field
`CoefficientNormCharts.Controls`, the geometry order `s+2` estimate, strong
kernel measurability, and the rough half-order amplitude bound. Constants,
low reserves, the derivative shift fourteen, and domains precede `F`, the
initial scalar and all high norms. The hypotheses about coefficients, flow
maps, and scalar/null smoothness are the exact outputs of
`exists_projected_local_positive_amplitude` for the SAME maps retained by the
parent. No norm bound on any desired primitive is assumed.

The parent still supplies the conic buffer containments and instantiates the
retained actual construction; this theorem makes no carrier operator or
unconditional continuum-row assertion. Source:
`app:ch_background:eq:bg-mixed-input`, `bg-T`, `bg-full-complex-amplitude`. -/
theorem exists_canonical_primitive_controls {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z : Euclidean 3) {ρ R τ : ℝ}
    (hρ : 0 < ρ) (hR : 0 < R) (hτ : 0 < τ) (hτR : τ ≤ R / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
      (closedBall ((0 : Euclidean n), z) ρ))
    (A H : ℕ → ℝ) (hA : ∀ j, 0 < A j) (hH : ∀ j, 0 < H j)
    (Dc : CoefficientNormCharts n)
    {X : Set (Euclidean n)} {V : Set CarrierParameter}
    (hX : IsOpen X) (hV : IsOpen V) (hXU : X ⊆ U)
    (haX : closedBall Dc.field.center.1 Dc.field.radius ⊆ X)
    (haV : closedBall Dc.field.center.2 Dc.field.radius ⊆ V)
    (haK : closedBall Dc.field.center.1 Dc.field.radius ⊆ K)
    (hc : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      (X ×ˢ V) (ball (0 : Euclidean n) T.physicalRadius ×ˢ
        parameterInterior (2 * P.radius)))
    (hLW : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      Dc.field.carrier
      ((coordinates (adaptedCoordinates T.data.adapted)).symm ''
        (Icc (-τ / 2) (τ / 2) ×ˢ closedBall ((0 : Euclidean (n - 1)), z) (R / 64))))
    (hregion : MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2))
      (X ×ˢ V) (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 32)))
    (hfieldRegion : Dc.field.region ⊆ X ×ˢ V)
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
    (hsupport : tsupport (FixedCutoffs.physical (n := n) hr 1) ×ˢ Zp ⊆ Dc.field.carrier)
    {M₁₅ Mᵣ κmet κ : ℝ} (hM₁₅ : 0 ≤ M₁₅) (hMᵣ : 0 ≤ Mᵣ)
    (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ δ > 0, ∃ M > 0, ∃ Cmask ≥ 0, ∃ B : ℕ → ℝ, (∀ j, 1 ≤ B j) ∧
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
      ∀ (row col : Fin n) (D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)))
        (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ),
      let p₀ := ((0 : Euclidean (n - 1)), z)
      let C := coordinates (adaptedCoordinates T.data.adapted)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      let Bρ := closedBall ((0 : Euclidean n), z) ρ
      let α := carrierScalarAmplitude T Q F row col Φ Y initial
      let b := fun w ↦ α w • carrierNullvector T Q col w
      IsOpen D → Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D →
      D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4) →
      MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) D →
      MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) →
      ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) →
      ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) →
      (∀ w ∈ Bρ, ContDiffAt ℝ ∞ (carrierNullvector T Q col) w ∧
        ContDiffAt ℝ ∞ (carrierTransportDirection T Q row col) w ∧
        ContDiffAt ℝ ∞ (carrierTransportPotential T Q F row col) w) →
      (∀ j, cNorm Bρ j (carrierNullvector T Q col) +
        cNorm Bρ j (carrierConullvector T Q row) +
        cNorm Bρ j (carrierAdaptedDenominator T Q row col) +
        cNorm Bρ j (fun w ↦ (carrierAdaptedDenominator T Q row col w)⁻¹) +
        cNorm Bρ j (carrierTransportDirection T Q row col) +
        cNorm Bρ j (carrierTransportPotential T Q F row col) ≤ A j * (1 + cNorm K (j + 5) F)) →
      (∀ j, cNorm J j Φ + cNorm J j Y ≤ H j * (1 + cNorm K (j + 5) F)) →
      ContDiffOn ℝ ∞ initial (ball p₀ (R / 4)) →
      ContDiffOn ℝ ∞ α (C ⁻¹' D) → ContDiffOn ℝ ∞ b (C ⁻¹' D) →
      cNorm (closedBall p₀ (R / 8)) 15 initial ≤ Mᵣ →
      let e := data T Q F row col Φ Y initial hr hcell angular FixedCutoffs.highFrequency
      StronglyMeasurable (Function.uncurry (carrierKernel e)) ∧
      (∀ x u, ‖carrierAmplitude e x u‖ ≤ Cmask * Real.sqrt ‖u.2‖) ∧
      ContDiffOn ℝ ∞ (transportPosition T Q) Dc.field.region ∧
      cNorm Dc.field.carrier 3 (transportPosition T Q) ≤ M ∧
      ∀ s, let Hhigh := 1 + cNorm K (s + 14) F +
        cNorm (closedBall p₀ (R / 8)) (s + 14) initial
      Dc.Controls s M (B s) Hhigh
        (TransportKernel.coefficientsOfCarrier e (FixedCutoffs.physical hr 1)) ∧
      1 + cNorm Dc.field.carrier (s + 2) (transportPosition T Q) ≤ B s * Hhigh := by
  have hL : IsCompact Dc.field.carrier := isCompact_closedBall ..
  have hLXV : Dc.field.carrier ⊆ X ×ˢ V :=
    Dc.field.ball_subset.trans hfieldRegion
  have hLO : Dc.field.carrier ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)) := fun p hp ↦ hc (hLXV hp)
  obtain ⟨Mn, hMn, Bn, hBn, hn⟩ := exists_projected_normalField_bounds T (N := N)
    hP hK hKU hball z hρ hR hτ hτR hbuffer A H hA hH
    Dc.field.center Dc.field.radius_pos hX hV hXU haX haV haK hc hLW hregion
    hM₁₅ hMᵣ hκmet hκ
  obtain ⟨δ, Mq, Bq, hδ, hMq, hBq, hq⟩ := exists_projected_canonical_quadratic_bounds T (N := N)
    hP adet hρdet hx hc₀ hL hLa hK hKU hball M₁₅ hκmet hκ
  obtain ⟨Mp, hMp, Bp, hBp, hp⟩ := exists_projected_transportPosition_primitive_bounds T (N := N)
    hP hL hLO hK hKU hball hM₁₅ hκmet hκ
    (closedBall ((0 : Euclidean (n - 1)), z) (R / 8))
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
  refine ⟨δ, hδ, M, hM, Cmask, hCmask, B, hB, ?_⟩
  intro Q F hQ hF hi hrank hFM hmet hnormal hclose row col D Φ Y initial
  dsimp only
  intro hD hsmall hbig hΦD hYU hΦ hY hreg hcoeff hflow hinitial hα hbreg hrM
  let e := data T Q F row col Φ Y initial hr hcell angular FixedCutoffs.highFrequency
  let q := fun p : Euclidean n × CarrierParameter ↦
    quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2))
  obtain ⟨hnreg, hnlow, hnhigh⟩ := hn Q F hQ hF hi hrank hFM hmet hnormal row col D Φ Y initial
    hD hsmall hbig hΦD hYU hΦ hY hreg hcoeff hflow hinitial hα hbreg hrM
  have hnreg' := hnreg.mono hfieldRegion
  have hqreg : ContDiffOn ℝ ∞ q Dc.field.region :=
    (quadratic_canonical_smooth T hP Q).mono (fun p hp ↦
      ⟨⟨hXU (hfieldRegion hp).1, (hc (hfieldRegion hp)).1⟩, (hc (hfieldRegion hp)).2⟩)
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
  · exact stronglyMeasurable_carrierKernel_of_local_primitives T Q F row col Φ Y initial
      hr hcell angular Dc.field.isOpen_region hpred.continuousOn hnreg'.continuousOn
      hqreg.continuousOn hang.continuous hangular (hsupport.trans Dc.field.ball_subset)
  · exact norm_carrierAmplitude_le_of_primitive_norms T Q F row col Φ Y initial hr hcell angular
      Dc.field hZp hangular hang hsupport hnreg' hqreg hMn.le hMq.le hnlow hqlow
  · intro s
    let W := 1 + cNorm K (s + 14) F +
      cNorm (closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) (s + 14) initial
    have hW : 1 ≤ W := by
      dsimp [W]
      linarith [cNorm_nonneg K (s + 14) F,
        cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) (s + 14) initial]
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
        (Function.uncurry (normalField T Q F row col Φ Y initial)) ≤ (1 + Bn s) * W := by
      have hh := hnhigh s
      change cNorm Dc.field.carrier s _ ≤ Bn s * W at hh
      nlinarith
    have hqh : cNorm Dc.field.carrier s (fun p ↦ (q p).ofLp) ≤ Bq s * W := by
      have hh := (le_add_of_nonneg_left (cNorm_nonneg Dc.field.carrier s q)).trans (hqq.2 s)
      apply hh.trans
      apply mul_le_mul_of_nonneg_left _ (hBq s).le
      have ho : cNorm K (s + 4) F ≤ cNorm K (s + 14) F := cNorm_mono_order (by omega)
      have h0 := cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), z) (R / 8)) (s + 14) initial
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

end JanetCartan.ContinuumRow.CanonicalCarrier
