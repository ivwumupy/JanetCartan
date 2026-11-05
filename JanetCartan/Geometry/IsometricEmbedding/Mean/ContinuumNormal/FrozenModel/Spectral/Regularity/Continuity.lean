module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity.Primitive
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.PuncturedSupport

/-!
# Continuity across the frozen inverse-chart boundary

The closed original angular support has a proved punctured image buffer.
The original high cutoff removes a neighborhood of zero physical frequency
by the transverse comparison. These two facts justify zero extension of the
literal frozen density in `app:ch_background:prop:bg-frame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
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


include hηb hr hInv htrans

/-- The actual transverse comparison bounds the inverse covector from above
in physical frequency. This is the low-frequency companion to
`frozenInverse_frequency_comparison` (`app:ch_background:eq:bg-Psi`). -/
theorem frozenInverse_inputFrequency_le {p : Variables n × Euclidean 2}
    (hp : p ∈ Ω₀) :
    ‖(u₀ p).2‖ ≤ (2 * ‖(adaptedSliceCoordinates T).equiv.toContinuousLinearMap‖) * ‖p.1.2.2‖ := by
  have hm := symbolInverse_maps T Q hηb hr hInv htrans hp
  have ht := htrans (p.2, 0, 0) hm.1 (u₀ p) hm.2
  have he : adaptedTransportChart T Q (p.2, 0, 0) (u₀ p) =
      (adaptedSliceCoordinates T).equiv p.1.2.2 := by
    change (adaptedSliceCoordinates T).equiv
      (transportAveragedGradient (transportPosition T Q)
        (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)) (originOutput p))) = _
    rw [transportAveragedGradient_symbolInverse T Q hηb hr hInv htrans hp]
    rfl
  have hdiff := norm_sub_norm_le ((u₀ p).2)
    (adaptedTransportChart T Q (p.2, 0, 0) (u₀ p)).2
  rw [norm_sub_rev] at hdiff
  have hsmall := (angularWidth_spec hηb hr).2.1
  have hsecond : ‖(adaptedTransportChart T Q (p.2, 0, 0) (u₀ p)).2‖ ≤
      ‖(adaptedSliceCoordinates T).equiv.toContinuousLinearMap‖ * ‖p.1.2.2‖ := by
    apply (norm_snd_le _).trans
    rw [he]
    exact (adaptedSliceCoordinates T).equiv.toContinuousLinearMap.le_opNorm _
  nlinarith [norm_nonneg ((u₀ p).2)]

include hP ha har hcarrier hf hcJ hV hLV

omit hP har hcarrier hf hcJ hV hLV in
/-- The original high mask makes the literal density zero at sufficiently
small output frequency; no cutoff in physical frequency is substituted
(`app:ch_background:defn:bg-row`). -/
theorem frozenExtendedDensity_zero_of_small_frequency
    (p : Variables n × Euclidean 2)
    (hp : (2 * ‖(adaptedSliceCoordinates T).equiv.toContinuousLinearMap‖) * ‖p.1.2.2‖ ≤ 1) :
    extendedDensity aᵢ J₀ u₀ Ω₀ p = 0 := by
  by_cases hm : p ∈ Ω₀
  · have hhi := FixedCutoffs.highFrequency_zero
      ((frozenInverse_inputFrequency_le T Q hηb hr hInv htrans hm).trans hp)
    simp only [extendedDensity, indicator_of_mem hm, inputDensity, inputWeight,
      uncutFrozenCoefficients, inverseCoordinates, hhi, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_mul, zero_div, zero_smul]
  · exact indicator_of_notMem hm _

omit hP hcarrier hcJ in
/-- Smoothness in physical frequency and the original spectator of the
literal frozen zero extension, including both the cone boundary and the
frequency origin (`app:ch_background:prop:bg-frame`, frozen step). -/
theorem frozenExtendedDensity_contDiff_of_primitiveRegularity
    (hreg : PrimitiveRegularity aᵢ J₀ (frozenInputDomain z₀ ηb r (6 * a))) :
    ContDiff ℝ ∞ (fun q : Euclidean n × Euclidean 2 ↦
      extendedDensity aᵢ J₀ u₀ Ω₀ ((0, 0, q.1), q.2)) := by
  let e : Euclidean n × Euclidean 2 → Variables n × Euclidean 2 :=
    fun q ↦ ((0, 0, q.1), q.2)
  have he : ContDiff ℝ ∞ e :=
    (contDiff_const.prodMk (contDiff_const.prodMk contDiff_fst)).prodMk contDiff_snd
  let f : Euclidean n × Euclidean 2 → Matrix (Fin n) (Fin n) ℝ :=
    fun q ↦ extendedDensity aᵢ J₀ u₀ Ω₀ (e q)
  have hΩ : IsOpen (e ⁻¹' Ω₀) :=
    (frozenSymbolDomain_open T Q hηb hr hInv htrans hV hLV).preimage he.continuous
  have hs : ContDiffOn ℝ ∞ f (e ⁻¹' Ω₀) := by
    have hd := ((inputDensity_contDiffOn hreg).comp
      (inverseCoordinates_contDiffOn (frozenSymbolInverse_smooth T Q hηb hr hInv htrans hLV))
      (frozenSymbolInverse_maps T Q hηb hr hInv htrans)).comp
      (s := e ⁻¹' Ω₀) (f := e) he.contDiffOn (fun _ hp ↦ hp)
    apply hd.congr
    intro q hq
    change extendedDensity aᵢ J₀ u₀ Ω₀ (e q) = _
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
      change extendedDensity aᵢ J₀ u₀ Ω₀ (e q) = 0
      simp only [extendedDensity, indicator_of_mem hqΩ]
      change inputDensity aᵢ J₀ p = 0
      simp [inputDensity, inputWeight, uncutFrozenCoefficients, hz]
    have hm := angularMask_nonzero z₀ (NormedSpace.normalize ηb) ha
      (angularWidth_spec hηb hr).1 hang
    have hpne : p.2.2 ≠ 0 := hp.2.2.1
    have hpK : p ∈ conicMaskSupport z₀ ηb r a :=
      ⟨⟨mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩,
        ⟨ball_subset_closedBall hm.1, ball_subset_closedBall hm.2.1⟩, hpne,
        mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hpne),
        ball_subset_closedBall hm.2.2⟩
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
      exact frozenExtendedDensity_zero_of_small_frequency T Q F row col Φ Y initial hηb hr ha
        hInv htrans (e w) hw.le
    exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hq
  exact conicMaskImage_punctured_buffer T Q hηb hr ha har' htrans hf
    ⟨hclosure hq, hne⟩

/-- The primitive smoothness hypothesis in the boundary-extension argument
is discharged for the actual unit-initial frozen normal and detector
(`new:lem:scaling`, `app:ch_background:prop:bg-frame`). -/
theorem frozenExtendedDensity_unit_contDiff :
    ContDiff ℝ ∞ (fun q : Euclidean n × Euclidean 2 ↦
      extendedDensity a₀ J₀ u₀ Ω₀ ((0, 0, q.1), q.2)) :=
  frozenExtendedDensity_contDiff_of_primitiveRegularity T Q F row col Φ Y (fun _ ↦ 1)
    hηb hr ha har hf hInv htrans hV hLV
    (frozenPrimitiveRegularity_unit T Q hP hηb hr ha har hcarrier
      hf hInv htrans hcJ F row col Φ Y)

end JanetCartan.ContinuumNormal.FrozenModel
