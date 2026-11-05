module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity.Continuity

/-!
# Permitted initial multipliers in the frozen spectator symbols

The initial amplitude remains the literal `initial (Y (0,(0,z)))`. Its
smoothness and compact bound follow from smooth initial data and the retained
flow's smoothness and range, exactly the analytic outputs/inputs of
`NullTransport.exists_projected_local_positive_amplitude` in
`ActualAmplitude.LocalConstruction`. The initial section must fit inside that
retained flow domain; this geometric containment remains explicit for the
parent's finite-family choice of radii. No normal, density, integrability,
or symbol estimate is assumed (`new:lem:scaling`, `bg-full-complex-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    {c C : ℝ} (hP : P.IsValid c C)
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hcJ : 0 < cJ) (hV : IsOpen V) (hLV : L ⊆ V)

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) ha
  (And.left (angularWidth_spec hηb hr))
local notation "a₀" => uncutFrozenCoefficients T Q F row col Φ Y (fun _ ↦ 1)
  angular₀ FixedCutoffs.highFrequency
local notation "aᵢ" => uncutFrozenCoefficients T Q F row col Φ Y initial
  angular₀ FixedCutoffs.highFrequency
local notation "J₀" => transportAbsoluteJacobian (adaptedSliceCoordinates T)
  (normalizedTransportPosition T Q 0)
local notation "u₀" => frozenSymbolInverse T Q z₀ ηb r (6 * a)
local notation "Ω₀" => frozenSymbolDomain T Q z₀ ηb r (6 * a)
local notation "S₀" => closedBall (spectatorCenter z₀) (a / 2)


/-- Exact fourth-power scaling of the original density by the retained
initial multiplier, before inverse substitution or integration
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenInputDensity_initial_factor (J : InputVariables n → ℝ) (p : InputVariables n) :
    inputDensity aᵢ J p = initial (Y (0, (0, parameter p.2.1))) ^ 4 • inputDensity a₀ J p := by
  ext i j
  simp only [inputDensity, inputWeight, uncutFrozenCoefficients,
    frozenSeedNormal_initial_factor T Q F row col Φ Y initial, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, Matrix.smul_apply, smul_eq_mul]
  ring

include hP hηb hr ha har hcarrier hf hInv htrans hcJ hV hLV

/-- Literal integrability, continuity and a uniform frequency bound for
permitted initial multipliers. All coefficient regularity and estimates are
derived from the primitive initial datum and retained flow. The input and
spectator domains, inverse, masks, and Lebesgue measure are unchanged
(`new:lem:scaling`, `app:ch_background:prop:bg-frame`). -/
theorem canonicalFrozenCarrierSymbol_initial_regularity
    {D : Set (Euclidean (n - 1) × Euclidean 3)}
    {Dflow : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hi : ContDiffOn ℝ ∞ initial D) (hY : ContDiffOn ℝ ∞ Y Dflow)
    (hseed : MapsTo (fun z : CarrierParameter ↦ ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter z)))
      (ball (z₀ 0) r ×ˢ ball (spectatorCenter z₀) (6 * a)) Dflow)
    (hYrange : MapsTo Y Dflow D) :
    (∀ p : Variables n, Integrable (fun v ↦ extendedDensity aᵢ J₀ u₀ Ω₀ (p, v))
      (volume.restrict S₀)) ∧
    Continuous (canonicalFrozenCarrierSymbol T Q F row col Φ Y initial z₀ hηb hr ha) ∧
    ∃ B ≥ (0 : ℝ), ∀ k,
      ‖canonicalFrozenCarrierSymbol T Q F row col Φ Y initial z₀ hηb hr ha k‖ ≤ B := by
  let Z := ball (z₀ 0) r ×ˢ ball (spectatorCenter z₀) (6 * a)
  have hZ : Z ⊆ parameter ⁻¹' parameterInterior (2 * P.radius) := by
    intro z hz i
    have hm := hcarrier (a := (z.2, z.1))
      ⟨(ball_subset_closedBall.trans (closedBall_subset_closedBall har)) hz.2,
        (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) hz.1⟩ i
    change |parameter z i| < 3 * P.radius / 2 at hm
    exact hm.trans_le (by linarith [hP.1])
  have hW : MapsTo (fun p : InputVariables n ↦ p.2.1)
      (frozenInputDomain z₀ ηb r (6 * a)) Z := fun _ hp ↦ ⟨hp.2.1, hp.1.1⟩
  have hS : carrierSupport z₀ (r := a) ⊆ Z := by
    intro z hz
    exact ⟨closedBall_subset_ball (by linarith) hz.1,
      closedBall_subset_ball (by linarith) hz.2⟩
  have hseedSmooth : ContDiff ℝ ∞
      (fun z : CarrierParameter ↦ ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter z))) :=
    contDiff_const.prodMk (contDiff_const.prodMk parameter.contDiff)
  have hYs := hY.comp hseedSmooth.contDiffOn hseed
  have hYD := hYrange.comp hseed
  have hn := (frozenSeedNormal_smooth T Q F row col Φ Y hP initial hi hZ hYs hYD).comp
    contDiffOn_snd.fst hW
  have hu := frozenPrimitiveRegularity_unit T Q hP hηb hr ha har hcarrier
    hf hInv htrans hcJ F row col Φ Y
  have hreg : PrimitiveRegularity aᵢ J₀ (frozenInputDomain z₀ ηb r (6 * a)) :=
    ⟨hu.leftMeasurement, hu.rightMeasurement, hu.angular, hu.high, hn, hn,
      hu.leftReduced, hu.rightReduced, hu.jacobian, hu.jacobian_ne_zero, hu.covector_ne_zero⟩
  have hmeas : StronglyMeasurable (extendedDensity aᵢ J₀ u₀ Ω₀) := by
    classical
    let : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _
    let : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩
    have hd := ((inputDensity_contDiffOn hreg).comp
      (inverseCoordinates_contDiffOn (frozenSymbolInverse_smooth T Q hηb hr hInv htrans hLV))
      (frozenSymbolInverse_maps T Q hηb hr hInv htrans)).continuousOn
    exact (hd.measurable_piecewise continuousOn_const
      (frozenSymbolDomain_open T Q hηb hr hInv htrans hV hLV).measurableSet).stronglyMeasurable
  have hβ : ContinuousOn (fun z : CarrierParameter ↦ initial (Y (0, (0, parameter z))) ^ 4)
      (carrierSupport z₀ (r := a)) := ((hi.comp hYs hYD).pow 4).continuousOn.mono hS
  obtain ⟨M, hM⟩ := (carrierSupport_compact z₀ (r := a)).exists_bound_of_continuousOn hβ
  obtain ⟨B, hB, hb⟩ := exists_frozenExtendedDensity_unit_bound T Q F row col Φ Y hP hηb hr ha
    har hcarrier hf hInv htrans hcJ
  let B' := max 0 M * B
  have hB' : 0 ≤ B' := mul_nonneg (le_max_left _ _) hB
  have hbound (p : Variables n × Euclidean 2) : ‖extendedDensity aᵢ J₀ u₀ Ω₀ p‖ ≤ B' := by
    by_cases hp : p ∈ Ω₀
    · by_cases hm : angular₀ ((u₀ p).1, p.2) (‖(u₀ p).2‖⁻¹ • (u₀ p).2) = 0
      · simpa [extendedDensity, hp, inputDensity, inputWeight, uncutFrozenCoefficients,
          inverseCoordinates, hm] using hB'
      have hz := angularMask_nonzero z₀ (NormedSpace.normalize ηb) ha
        (angularWidth_spec hηb hr).1 hm
      have hβbound := (hM ((u₀ p).1, p.2) ⟨ball_subset_closedBall hz.1,
        ball_subset_closedBall hz.2.1⟩).trans (le_max_right 0 M)
      have he : extendedDensity aᵢ J₀ u₀ Ω₀ p =
          initial (Y (0, (0, parameter ((u₀ p).1, p.2)))) ^ 4 • extendedDensity a₀ J₀ u₀ Ω₀ p := by
        simp only [extendedDensity, indicator_of_mem hp]
        exact frozenInputDensity_initial_factor T Q F row col Φ Y initial hηb hr ha J₀ _
      rw [he, norm_smul]
      exact mul_le_mul hβbound (hb p) (norm_nonneg _) (le_max_left _ _)
    · simpa only [extendedDensity, indicator_of_notMem hp, norm_zero] using hB'
  have hint (p : Variables n) : Integrable (fun v ↦ extendedDensity aᵢ J₀ u₀ Ω₀ (p, v))
      (volume.restrict S₀) := by
    apply Measure.integrableOn_of_bounded (isCompact_closedBall _ _).measure_lt_top.ne
      ((hmeas.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun v ↦ hbound (p, v)
  have hcont := frozenExtendedDensity_contDiff_of_primitiveRegularity T Q F row col Φ Y initial
    hηb hr ha har hf hInv htrans hV hLV hreg
  have hK : IsCompact S₀ := isCompact_closedBall _ _
  have : IsFiniteMeasure (volume.restrict S₀) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hcontAmp : ContDiff ℝ ∞ (fun k : Euclidean n ↦ amplitude aᵢ J₀ u₀ Ω₀ S₀ (0, 0, k)) := by
    apply contDiffOn_univ.mp
    exact contDiffOn_compactParameterIntegral (μ := volume) isOpen_univ isOpen_univ hK
      (subset_univ S₀) hcont.contDiffOn
  refine ⟨hint, (continuous_const (y := (2 * (2 * Real.pi) ^ n : ℝ))).smul
    (hcontAmp.continuous.add (hcontAmp.continuous.comp continuous_neg)), ?_⟩
  have hiAmp (p : Variables n) : ‖amplitude aᵢ J₀ u₀ Ω₀ S₀ p‖ ≤ B' * volume.real S₀ := by
    apply norm_setIntegral_le_of_norm_le_const_ae' hK.measure_lt_top
    exact Filter.Eventually.of_forall fun v _ ↦ hbound (p, v)
  refine ⟨(2 * (2 * Real.pi) ^ n) * (2 * (B' * volume.real S₀)), by positivity, fun k ↦ ?_⟩
  change ‖(2 * (2 * Real.pi) ^ n) •
    (amplitude aᵢ J₀ u₀ Ω₀ S₀ (0, 0, k) + amplitude aᵢ J₀ u₀ Ω₀ S₀ (0, 0, -k))‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_add_le _ _).trans ((add_le_add (hiAmp (0, 0, k)) (hiAmp (0, 0, -k))).trans_eq (by ring))

end JanetCartan.ContinuumNormal.FrozenModel
