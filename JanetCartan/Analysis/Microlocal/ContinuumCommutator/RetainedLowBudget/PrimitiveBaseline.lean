module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.Controls

/-!
# The supported carrier primitive baseline

This is a deduction from the uniform full-normal bound proved by
`RetainedLowBudget.exists_initialized_retained_leading_density_low_bounds`.
It derives every original coefficient norm at order `μ+1` and the transported
position at order `μ+3`, without a higher scalar budget. Fixed masks, the
actual projected detector and the Hamilton covector derivative are unchanged.
The supported same-mask construction consumes this for
`app:ch_background:eq:bg-commutator`. Its geometric instantiation and the
connection to the initialized row are separate obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumCommutator.RetainedLowBudget
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open ActualFlow FlowAmplitude ProjectedStressFrame ContinuumRow
open CanonicalCarrier LeadingPrimitive LeadingWave.FullModulation
open ContinuumNormalReduction.TransportSymbol

private theorem controls_one_enlarge {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {D : PrimitiveNormChart E} {s : ℕ} {M M' B B' : ℝ} {f : E → G}
    (h : D.Controls s M B 1 f) (hM : M ≤ M') (hB : B ≤ B') :
    D.Controls s M' B' 1 f :=
  ⟨h.smooth, h.low.trans hM, h.high.trans (mul_le_mul_of_nonneg_right hB zero_le_one)⟩

/-- The same five coefficients and transported position have the required
uniform finite bounds. The only full-normal bound is produced, with the
original positive scalar, by the initialized theorem named above; the carrier
normal follows by the original graph. The remaining fields come from their
concrete formulas. The detector threshold precedes all source budgets.
This conditional deduction is not the unconditional retained-amplitude bound
(`app:ch_background:eq:bg-mixed-input`, `app:ch_background:eq:bg-commutator`). -/
theorem exists_retained_primitive_low_controls {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
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
 :
    ∃ δ > 0,
      ∀ (MF Bnormal κmet κ : ℝ), 0 ≤ MF → 0 ≤ Bnormal → 0 < κmet → 0 < κ →
      ∃ M > 0, ∃ B ≥ (1 : ℝ),
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N), Q.1 = projectedStress F →
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm K (2 * (n + 1) + 14) F ≤ MF →
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
      cNorm J (2 * (n + 1) + 1) (fullNormal T Q F row col Φ Y initial) ≤ Bnormal →
      let e := data T Q F row col φ y initial hr hcell angular FixedCutoffs.highFrequency
      ContDiffOn ℝ ∞ (transportPosition T Q) Dc.field.region ∧
      cNorm Dc.field.carrier 3 (transportPosition T Q) ≤ M ∧
      Dc.Controls (2 * (n + 1) + 1) M B 1
        (TransportKernel.coefficientsOfCarrier e (FixedCutoffs.physical hr 1)) ∧
      1 + cNorm Dc.field.carrier (2 * (n + 1) + 1 + 2) (transportPosition T Q) ≤ B := by
  let p := 2 * (n + 1) + 1
  have hL : IsCompact Dc.field.carrier := isCompact_closedBall ..
  have hparameter : Dc.field.region ⊆ univ ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)) := fun q hq ↦ ⟨mem_univ _, (hfield hq).2⟩
  have hLO : Dc.field.carrier ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)) :=
    fun q hq ↦ ⟨(hfield (Dc.field.ball_subset hq)).1.2, (hfield (Dc.field.ball_subset hq)).2⟩
  obtain ⟨δ, _Mq, hδ, _hMq, hq⟩ := exists_projected_canonical_quadratic_bounds_before_geometry
    T (N := N) hP adet hρdet hx hc₀ hL hLa hK hKU hball
  obtain ⟨An, hAn, hn⟩ := exists_normalField_pullback_bounds T (N := N)
    hP Dc.field hparameter hJ hgraph
  obtain ⟨Mm, hMm, Bm, hBm, hm⟩ := exists_fixedMask_controls Dc hr angular hang.contDiffOn
  refine ⟨δ, hδ, ?_⟩
  intro MF Bnormal κmet κ hMF hBnormal hκmet hκ
  obtain ⟨Aq, hAq, hq⟩ := hq MF κmet κ hκmet hκ
  obtain ⟨Ap, hAp, hp⟩ := exists_projected_transportPosition_bound T (N := N)
    hP hL hLO hK hKU hball MF hκmet hκ
  let Nbound := An p * Bnormal
  let Qbound := Aq p * (1 + MF)
  let Pbound := Ap (p + 2) * (1 + MF)
  have hNbound : 0 ≤ Nbound := mul_nonneg (hAn p).le hBnormal
  have hQbound : 0 ≤ Qbound := mul_nonneg (hAq p).le (by positivity)
  have hPbound : 0 ≤ Pbound := mul_nonneg (hAp (p + 2)).le (by positivity)
  let M := 1 + Mm + Nbound + Qbound + Pbound
  let Bbudget := 1 + Bm p + Nbound + Qbound + Pbound
  refine ⟨M, by dsimp [M]; linarith, Bbudget,
    by dsimp [Bbudget]; linarith [hBm p], ?_⟩
  intro Q F hQ hF hi hrank hFM hmet hnormal hclose row col Φ Y φ y initial O V
    hO hxO hphase hJO hregion hcomp hnull hcompat hfull
  dsimp only
  let q := fun w : Euclidean n × CarrierParameter ↦
    quadratic (Q.1 w.1) (T.carrierGradient Q w.1 (parameter w.2))
  obtain ⟨hnreg, hnhigh⟩ := hn Q F row col Φ Y φ y initial O V
    hO hxO hphase hJO hregion hcomp hF hi hrank hnull hcompat
  have hnh : cNorm Dc.field.carrier p
      (Function.uncurry (normalField T Q F row col φ y initial)) ≤ Nbound :=
    (hnhigh p).trans (mul_le_mul_of_nonneg_left hfull (hAn p).le)
  have hqreg : ContDiffOn ℝ ∞ q Dc.field.region :=
    (quadratic_canonical_smooth T hP Q).mono hfield
  have hpred := (transportPosition_smooth T Q hP).mono hphaseRegion
  have hfour : cNorm K 4 F ≤ MF := (cNorm_mono_order (by omega)).trans hFM
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
  have hpp := hp F hF hi hrank hfour hmet hnormal hlow
  dsimp only at hqq hpp
  rw [hQeq, ← hQ] at hqq
  rw [hQeq] at hpp
  have hqh : cNorm Dc.field.carrier p (fun w ↦ (q w).ofLp) ≤ Qbound :=
    ((le_add_of_nonneg_left (cNorm_nonneg ..)).trans (hqq.2 p)).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        ((cNorm_mono_order (by dsimp [p]; omega)).trans hFM)) (hAq p).le)
  have hph : cNorm Dc.field.carrier (p + 2) (transportPosition T Q) ≤ Pbound :=
    (hpp (p + 2)).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      ((cNorm_mono_order (by dsimp [p]; omega)).trans hFM)) (hAp (p + 2)).le)
  have hNlow := (cNorm_mono_order (s := Dc.field.carrier)
    (f := Function.uncurry (normalField T Q F row col φ y initial))
    (by dsimp [p]; omega : 1 ≤ p)).trans hnh
  have hQlow := (cNorm_mono_order (s := Dc.field.carrier) (f := fun w ↦ (q w).ofLp)
    (by dsimp [p]; omega : 1 ≤ p)).trans hqh
  have hPlow := (cNorm_mono_order (s := Dc.field.carrier) (f := transportPosition T Q)
    (by dsimp [p]; omega : 3 ≤ p + 2)).trans hph
  obtain ⟨hm₁, hm₂, hm₃⟩ := hm p 1 le_rfl
  refine ⟨hpred, hPlow.trans (by dsimp [M]; linarith), ?_,
    by change 1 + cNorm Dc.field.carrier (p + 2) _ ≤ Bbudget
       dsimp [Bbudget]; linarith [hBm p]⟩
  rw [coefficientsOfCarrier_data]
  have hMmM : Mm ≤ M := by dsimp [M]; linarith
  have hBmB : Bm p ≤ Bbudget := by dsimp [Bbudget]; linarith
  refine ⟨controls_one_enlarge hm₁ hMmM hBmB,
    controls_one_enlarge hm₂ hMmM hBmB,
    controls_one_enlarge hm₃ hMmM hBmB, ?_, ?_⟩
  · refine ⟨hnreg, hNlow.trans (by dsimp [M]; linarith), ?_⟩
    change 1 + cNorm Dc.field.carrier p
      (Function.uncurry (normalField T Q F row col φ y initial)) ≤ Bbudget * 1
    simp only [mul_one]
    dsimp [Bbudget]
    linarith [hBm p]
  · refine ⟨PiLp.contDiff_ofLp.comp_contDiffOn hqreg,
      hQlow.trans (by dsimp [M]; linarith), ?_⟩
    change 1 + cNorm Dc.field.carrier p (fun w ↦ (q w).ofLp) ≤ Bbudget * 1
    simp only [mul_one]
    dsimp [Bbudget]
    linarith [hBm p]

end JanetCartan.ContinuumCommutator.RetainedLowBudget
