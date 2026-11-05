module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.Primitive
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedSupport

/-!
# Smooth zero extension for the retained frozen density

Monotonicity places the SAME smaller mask support in the outer punctured
image buffer. The original high cutoff removes the frequency origin. These
facts supply `retainedFrozenAmplitude_unit_contDiff`, retaining distinct
inner mask and outer inverse radii (`app:ch_background:prop:bg-frame`).
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

include hηb hr hInv htrans

/-- The original high mask makes the literal density zero at sufficiently
small output frequency; no cutoff in physical frequency is substituted
(`app:ch_background:defn:bg-row`). -/
theorem retainedFrozenExtendedDensity_zero_of_small_frequency
    (p : Variables n × Euclidean 2)
    (hp : (2 * ‖(adaptedSliceCoordinates T).equiv.toContinuousLinearMap‖) * ‖p.1.2.2‖ ≤ 1) :
    extendedDensity a₀ J₀ u₀ Ω₀ p = 0 := by
  by_cases hm : p ∈ Ω₀
  · have hhi := FixedCutoffs.highFrequency_zero
      ((frozenInverse_inputFrequency_le T Q hηb hr hInv htrans hm).trans hp)
    simp only [extendedDensity, indicator_of_mem hm, inputDensity, inputWeight,
      uncutFrozenCoefficients, inverseCoordinates, hhi, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_mul, zero_div, zero_smul]
  · exact indicator_of_notMem hm _

include ha har hf hInv htrans hV hLV hrr haa

/-- Smoothness in physical frequency and the original spectator of the
literal frozen zero extension, including both the cone boundary and the
frequency origin (`app:ch_background:prop:bg-frame`, frozen step). -/
theorem retainedFrozenExtendedDensity_contDiff_of_primitiveRegularity
    (hreg : PrimitiveRegularity a₀ J₀ (frozenInputDomain z₀ ηb r (6 * a))) :
    ContDiff ℝ ∞ (fun q : Euclidean n × Euclidean 2 ↦
      extendedDensity a₀ J₀ u₀ Ω₀ ((0, 0, q.1), q.2)) := by
  let e : Euclidean n × Euclidean 2 → Variables n × Euclidean 2 :=
    fun q ↦ ((0, 0, q.1), q.2)
  have he : ContDiff ℝ ∞ e :=
    (contDiff_const.prodMk (contDiff_const.prodMk contDiff_fst)).prodMk contDiff_snd
  let f : Euclidean n × Euclidean 2 → Matrix (Fin n) (Fin n) ℝ :=
    fun q ↦ extendedDensity a₀ J₀ u₀ Ω₀ (e q)
  have hΩ : IsOpen (e ⁻¹' Ω₀) :=
    (frozenSymbolDomain_open T Q hηb hr hInv htrans hV hLV).preimage he.continuous
  have hs : ContDiffOn ℝ ∞ f (e ⁻¹' Ω₀) := by
    have hd := ((inputDensity_contDiffOn hreg).comp
      (inverseCoordinates_contDiffOn (frozenSymbolInverse_smooth T Q hηb hr hInv htrans hLV))
      (frozenSymbolInverse_maps T Q hηb hr hInv htrans)).comp
      (s := e ⁻¹' Ω₀) (f := e) he.contDiffOn (fun _ hp ↦ hp)
    apply hd.congr
    intro q hq
    change extendedDensity a₀ J₀ u₀ Ω₀ (e q) = _
    exact indicator_of_mem (show e q ∈ Ω₀ from hq) _
  apply Localization.contDiff_of_contDiffOn_support_neighborhood hΩ hs
  have har' : a ≤ r := by linarith
  let K := augmentedTransportGradient (transportPosition T Q) '' conicMaskSupport z₀ ηb r a
  have hsupp : Function.support f ⊆ e ⁻¹' K := by
    intro q hq
    have hqΩ : e q ∈ Ω₀ := by
      by_contra h
      exact hq (indicator_of_notMem h _)
    let p := inverseCoordinates u₀ (e q)
    have hp := frozenSymbolInverse_maps T Q hηb hr hInv htrans hqΩ
    have hang : angular₀ p.2.1 (‖p.2.2‖⁻¹ • p.2.2) ≠ 0 := by
      intro hz
      apply hq
      change extendedDensity a₀ J₀ u₀ Ω₀ (e q) = 0
      simp only [extendedDensity, indicator_of_mem hqΩ]
      change inputDensity a₀ J₀ p = 0
      simp [inputDensity, inputWeight, uncutFrozenCoefficients, hz]
    have hm := angularMask_nonzero z₀ (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 hang
    have hpne : p.2.2 ≠ 0 := hp.2.2.1
    have hpKsmall : p ∈ conicMaskSupport z₀ ηb r' a' :=
      ⟨⟨mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩,
        ⟨ball_subset_closedBall hm.1, ball_subset_closedBall hm.2.1⟩, hpne,
        mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hpne),
        ball_subset_closedBall hm.2.2⟩
    have hpK := conicMaskSupport_mono z₀ ηb hrr haa hpKsmall
    refine ⟨p, hpK, ?_⟩
    exact augmentedTransportGradient_inverseCoordinates _ _
      (fun _ h ↦ transportAveragedGradient_symbolInverse T Q hηb hr hInv htrans h) hqΩ
  have hclosure : tsupport f ⊆ e ⁻¹' closure K :=
    closure_minimal (hsupp.trans (preimage_mono subset_closure))
      (isClosed_closure.preimage he.continuous)
  intro q hq
  have hne : q.1 ≠ 0 := by
    intro hz
    have hsmall : ∀ᶠ w : Euclidean n × Euclidean 2 in 𝓝 q,
        (2 * ‖(adaptedSliceCoordinates T).equiv.toContinuousLinearMap‖) * ‖w.1‖ < 1 := by
      apply (isOpen_lt (continuous_const.mul continuous_fst.norm) continuous_const).mem_nhds
      simp [hz]
    have hzero : f =ᶠ[𝓝 q] 0 := by
      filter_upwards [hsmall] with w hw
      exact retainedFrozenExtendedDensity_zero_of_small_frequency T Q F row col Φ Y hηb hr hr' ha'
        hInv htrans (e w) hw.le
    exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hq
  exact conicMaskImage_punctured_buffer T Q hηb hr ha har' htrans hf
    ⟨hclosure hq, hne⟩

include hP hcarrier hcJ

/-- The primitive smoothness hypothesis in the boundary-extension argument
is discharged for the actual unit-initial frozen normal and detector
(`new:lem:scaling`, `app:ch_background:prop:bg-frame`). -/
theorem retainedFrozenExtendedDensity_unit_contDiff :
    ContDiff ℝ ∞ (fun q : Euclidean n × Euclidean 2 ↦
      extendedDensity a₀ J₀ u₀ Ω₀ ((0, 0, q.1), q.2)) :=
  retainedFrozenExtendedDensity_contDiff_of_primitiveRegularity T Q F row col Φ Y
    hηb hr ha hr' ha' hrr haa har hf hInv htrans hV hLV
    (retainedFrozenPrimitiveRegularity_unit T Q F row col Φ Y hP hηb hr hr' ha' har hcarrier
      hf hInv htrans hcJ)


end JanetCartan.ContinuumNormal.RetainedFrozen
