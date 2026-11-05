module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.CanonicalData
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.PrincipalGap

/-!
# Nonvanishing of the actual frozen normal

The normal factor in `app:ch_background:eq:bg-full-complex-amplitude` is the
canonical completion of the SAME transported null column. The primitive
producer `LeadingWave.exists_principal_gap_threshold` supplies its gap from
immersion, full normal rank, frame closeness and the selected minor. At zero
physical position the unit initial amplitude is exactly one. These facts
supply the normal factor of the incidence weights in
`app:ch_background:prop:bg-frame`; no nonzero normal is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier
open NullTransport LeadingWave ProjectedStressFrame
open ContinuumNormalReduction TransportSymbol

section Multiplier
variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- At the frozen origin the literal normal density changes by the square
of the initial multiplier, evaluated at the SAME transport footpoint
(`app:ch_background:prop:bg-frame`, allowed initial-amplitude perturbations).
The time-zero identity for unit amplitude is `carrierScalarAmplitude_origin_unit`.
-/
theorem frozenNormal_norm_sq_multiplier (z : CarrierParameter) :
    ‖normalField T Q F row col Φ Y initial 0 z‖ ^ 2 =
      initial (Y (0, (0, parameter z))) ^ 2 *
        ‖normalField T Q F row col Φ Y (fun _ ↦ 1) 0 z‖ ^ 2 := by
  simpa only [FlowAmplitude.coordinates_apply, ActualFlow.adaptedCoordinates_apply,
    map_zero, inner_zero_right, Prod.fst_zero, Prod.snd_zero] using
    normalField_norm_sq_eq_density T Q F row col Φ Y initial 0 z

/-- The frozen scalar weight contains two squared normal factors, so the
allowed initial multiplier occurs to the fourth power. This is an identity
for the literal `inputWeight`, including its original Jacobian and masks
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenInputWeight_multiplier
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (J : InputVariables n → ℝ) (p : InputVariables n) :
    inputWeight (uncutFrozenCoefficients T Q F row col Φ Y initial angular high) J p =
      initial (Y (0, (0, parameter p.2.1))) ^ 4 *
        inputWeight (uncutFrozenCoefficients T Q F row col Φ Y (fun _ ↦ 1)
          angular high) J p := by
  simp only [inputWeight, uncutFrozenCoefficients,
    frozenNormal_norm_sq_multiplier T Q F row col Φ Y initial]
  ring

/-- A multiplier at least `1/2` preserves at least `1/16` of the literal
frozen weight. This retains the fourth power forced by the full normal
amplitude (`app:ch_background:prop:bg-frame`). -/
theorem frozenInputWeight_multiplier_lower_bound
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (J : InputVariables n → ℝ) (p : InputVariables n) (hJ : 0 ≤ J p)
    (hi : 1 / 2 ≤ initial (Y (0, (0, parameter p.2.1)))) :
    (1 / 16) * inputWeight (uncutFrozenCoefficients T Q F row col Φ Y (fun _ ↦ 1)
      angular high) J p ≤
      inputWeight (uncutFrozenCoefficients T Q F row col Φ Y initial angular high) J p := by
  rw [frozenInputWeight_multiplier T Q F row col Φ Y initial]
  have hw : 0 ≤ inputWeight (uncutFrozenCoefficients T Q F row col Φ Y (fun _ ↦ 1)
      angular high) J p := by
    dsimp [inputWeight, uncutFrozenCoefficients]
    positivity
  have hs : (1 / 4 : ℝ) ≤ initial (Y (0, (0, parameter p.2.1))) ^ 2 := by
    nlinarith
  have hfour : (1 / 16 : ℝ) ≤ initial (Y (0, (0, parameter p.2.1))) ^ 4 := by
    nlinarith [sq_nonneg (initial (Y (0, (0, parameter p.2.1))) ^ 2 - 1 / 4)]
  exact mul_le_mul_of_nonneg_right hfour hw

end Multiplier

/-- Construct a positive lower bound for the SAME frozen unit-amplitude
normal from the primitive projected-frame data and any retained minor.
All constants precede the immersion. The basis and null relation are proved
by `LeadingWave.exists_principal_gap_threshold`, and the unit scalar at zero
by `carrierScalarAmplitude_origin_unit`. This is the normal-factor producer
for the incidence-weight proof of `app:ch_background:prop:bg-frame`.

The quantitative minor hypothesis is supplied on its fixed open refinement
by `NullTransport.exists_actual_null_gaps`. It is not a nonvanishing-normal
assumption. The frame witness `hlow` is arbitrary, preserving the one already
used by `exists_constructed_incidence_detection`.
-/
theorem exists_frozen_unit_normal_gap {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    ∃ δ g : ℝ, 0 < δ ∧ 0 < g ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ M →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ (row col : Fin n)
          (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
          (z : CarrierParameter), parameter z ∈ parameterCube (3 * P.radius / 2) →
          μ ≤ |(reducedSymbol (Q.1 0) (T.carrierGradient Q 0 (parameter z))).adjugate row col| →
          g ≤ ‖normalField T Q F row col Φ Y (fun _ ↦ 1) 0 z‖ := by
  obtain ⟨δ, cξ, g, C, hδ, _hcξ, hg, _hC, hgap⟩ :=
    exists_principal_gap_threshold hn hP T hK hKU hball M hμ (by norm_num : (0 : ℝ) < 1)
  refine ⟨δ, g, hδ, hg, ?_⟩
  intro F hF hi hrank hM hclose hlow Q row col Φ Y z hz hminor
  obtain ⟨hlow', hbound⟩ := hgap F hF hi hrank hM hclose
  have h0 : (0 : Euclidean n) ∈ ball 0 T.physicalRadius := by
    simpa using T.physicalRadius_pos
  have h0K : (0 : Euclidean n) ∈ K :=
    hball (mem_closedBall_self T.data.localReference.stateRadius_pos.le)
  have hb := ((hbound 0 h0 h0K (parameter z) hz).2.2 row col hminor).2 1 le_rfl
  simpa only [normalField, carrierScalarAmplitude_origin_unit, one_smul] using hb

end JanetCartan.ContinuumNormal.FrozenModel
