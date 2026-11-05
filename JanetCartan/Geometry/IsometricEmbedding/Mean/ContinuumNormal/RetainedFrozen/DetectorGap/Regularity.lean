module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.Continuity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedSupport

/-!
# Spectator integration on the retained frozen masks

The proved density regularity and uniform bound give Bochner integrability
and a smooth spectator integral on exactly the closed ball of radius `a'/2`.
The consumer is `retainedFrozenMatrixSymbol_unit_continuous` and its bound
in `app:ch_background:prop:bg-frame`, Step 2.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen
open FrozenModel ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    {c C : ℝ} (hP : P.IsValid c C)
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har : 6 * a ≤ 3 * r)
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

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) ha'
  (And.left (angularWidth_spec hηb hr'))
local notation "a₀" => uncutFrozenCoefficients T Q F row col Φ Y (fun _ ↦ 1)
  angular₀ FixedCutoffs.highFrequency
local notation "J₀" => transportAbsoluteJacobian (adaptedSliceCoordinates T)
  (normalizedTransportPosition T Q 0)
local notation "u₀" => frozenSymbolInverse T Q z₀ ηb r (6 * a)
local notation "Ω₀" => frozenSymbolDomain T Q z₀ ηb r (6 * a)
local notation "S₀" => closedBall (spectatorCenter z₀) (a' / 2)

include hP hηb hr har hcarrier hf hInv htrans hcJ hV hLV

/-- The literal zero-extended unit-amplitude frozen density is measurable.
Smoothness inside the actual inverse domain and its openness suffice here;
continuity across its boundary is not assumed (`bg-full-complex-amplitude`). -/
theorem retainedFrozenExtendedDensity_unit_stronglyMeasurable :
    StronglyMeasurable (extendedDensity a₀ J₀ u₀ Ω₀) := by
  classical
  let : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _
  let : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩
  have hreg := retainedFrozenPrimitiveRegularity_unit T Q F row col Φ Y hP hηb hr hr' ha' har hcarrier
    hf hInv htrans hcJ
  have hd := ((inputDensity_contDiffOn hreg).comp
    (inverseCoordinates_contDiffOn (frozenSymbolInverse_smooth T Q hηb hr hInv htrans hLV))
    (frozenSymbolInverse_maps T Q hηb hr hInv htrans)).continuousOn
  exact (hd.measurable_piecewise continuousOn_const
    (frozenSymbolDomain_open T Q hηb hr hInv htrans hV hLV).measurableSet).stronglyMeasurable

include haa

/-- Integrability of the literal density at EVERY frequency, over precisely
`closedBall (spectatorCenter z₀) (a/2)` with Lebesgue measure. This supplies
actual Bochner integrability for the positivity consumer, rather than using
the convention for a divergent integral (`app:ch_background:prop:bg-frame`). -/
theorem retainedFrozenExtendedDensity_unit_integrable (p : Variables n) :
    Integrable (fun v ↦ extendedDensity a₀ J₀ u₀ Ω₀ (p, v)) (volume.restrict S₀) := by
  obtain ⟨B, _, hb⟩ := exists_retainedFrozenExtendedDensity_unit_bound T Q F row col Φ Y hP hηb hr hr' ha' haa
    har hcarrier hf hInv htrans hcJ
  apply Measure.integrableOn_of_bounded (isCompact_closedBall _ _).measure_lt_top.ne
    (((retainedFrozenExtendedDensity_unit_stronglyMeasurable T Q F row col Φ Y hP hηb hr hr' ha' har hcarrier
      hf hInv htrans hcJ hV hLV).comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun v ↦ hb (p, v)

include ha hrr

/-- The actual unit-amplitude spectator integral is smooth in physical
frequency, including zero and the inverse-chart boundary. Domination is
supplied by compactness and the proved joint density smoothness
(`app:ch_background:prop:bg-frame`, frozen step). -/
theorem retainedFrozenAmplitude_unit_contDiff :
    ContDiff ℝ ∞ (fun k : Euclidean n ↦ amplitude a₀ J₀ u₀ Ω₀ S₀ (0, 0, k)) := by
  have hK : IsCompact S₀ := isCompact_closedBall _ _
  have : IsFiniteMeasure (volume.restrict S₀) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  apply contDiffOn_univ.mp
  exact contDiffOn_compactParameterIntegral (μ := volume) isOpen_univ isOpen_univ hK
    (subset_univ S₀) (retainedFrozenExtendedDensity_unit_contDiff T Q F row col Φ Y hP hηb hr ha hr' ha' hrr haa har
      hcarrier hf hInv htrans hcJ hV hLV).contDiffOn

/-- Continuity of the SAME retained frozen carrier symbol at every physical
frequency, with both original reflections and Fourier normalization retained
(`app:ch_background:prop:bg-frame`). -/
theorem retainedFrozenCarrierSymbol_unit_continuous :
    Continuous (retainedFrozenCarrierSymbol T Q F row col Φ Y (fun _ ↦ 1) z₀ r a hηb hr' ha') := by
  have hs := (retainedFrozenAmplitude_unit_contDiff T Q F row col Φ Y hP hηb hr ha hr' ha' hrr haa har hcarrier
    hf hInv htrans hcJ hV hLV).continuous
  exact (continuous_const (y := (2 * (2 * Real.pi) ^ n : ℝ))).smul
    (hs.add (hs.comp continuous_neg))

omit ha hrr hV hLV in
/-- The actual reflected carrier symbol is uniformly bounded over all
physical Euclidean frequencies, retaining the angular/high masks, inverse,
Jacobian, reflection, and exact Fourier normalization
(`app:ch_background:prop:bg-frame`, frozen step). -/
theorem retainedFrozenCarrierSymbol_unit_bounded :
    ∃ B ≥ (0 : ℝ), ∀ k,
      ‖retainedFrozenCarrierSymbol T Q F row col Φ Y (fun _ ↦ 1) z₀ r a hηb hr' ha' k‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_retainedFrozenExtendedDensity_unit_bound T Q F row col Φ Y hP hηb hr hr' ha' haa
    har hcarrier hf hInv htrans hcJ
  have hi (p : Variables n) : ‖amplitude a₀ J₀ u₀ Ω₀ S₀ p‖ ≤ B * volume.real S₀ := by
    apply norm_setIntegral_le_of_norm_le_const_ae' (isCompact_closedBall _ _).measure_lt_top
    exact Filter.Eventually.of_forall fun v _ ↦ hb (p, v)
  refine ⟨(2 * (2 * Real.pi) ^ n) * (2 * (B * volume.real S₀)), by positivity, fun k ↦ ?_⟩
  change ‖(2 * (2 * Real.pi) ^ n) •
    (amplitude a₀ J₀ u₀ Ω₀ S₀ (0, 0, k) + amplitude a₀ J₀ u₀ Ω₀ S₀ (0, 0, -k))‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_add_le _ _).trans ((add_le_add (hi (0, 0, k)) (hi (0, 0, -k))).trans_eq (by ring))


end JanetCartan.ContinuumNormal.RetainedFrozen
