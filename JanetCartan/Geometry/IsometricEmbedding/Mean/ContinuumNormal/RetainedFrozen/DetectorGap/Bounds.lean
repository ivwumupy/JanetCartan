module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.Symbol
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedSupport

/-!
# Uniform bounds for the retained frozen density

The smaller mask support lies in the outer compact carrier support. The
existing normal, detector and Jacobian estimates then bound the literal
density at every frequency. The consumer is
`retainedFrozenCarrierSymbol_unit_bounded` (`app:ch_background:prop:bg-frame`).
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

include hP hr har hcarrier

private theorem retainedSeedTensor_bounded :
    ∃ B ≥ (0 : ℝ), ∀ z ∈ carrierSupport z₀ (r := a),
      ‖(‖normalField T Q F row col Φ Y (fun _ ↦ 1) 0 z‖ ^ 2 *
          ‖normalField T Q F row col Φ Y (fun _ ↦ 1) 0 z‖ ^ 2) •
        Matrix.vecMulVec (quadratic (Q.1 0) (T.carrierGradient Q 0 (parameter z))).ofLp
          (quadratic (Q.1 0) (T.carrierGradient Q 0 (parameter z))).ofLp‖ ≤ B := by
  let E : (Fin n → Fin n → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    LinearMap.toContinuousLinearMap LinearMap.id
  have hsub := frozenCarrierSupport_subset hP hr har hcarrier
  have hn := ((frozenSeedNormal_unit_smooth T Q F row col Φ Y hP).continuousOn.mono hsub).norm
  have hq := (PiLp.contDiff_ofLp.comp_contDiffOn
    (frozenSeedDetector_smooth T Q hP)).continuousOn.mono hsub
  have hv : ContinuousOn (fun z ↦ Matrix.vecMulVec
      (quadratic (Q.1 0) (T.carrierGradient Q 0 (parameter z))).ofLp
      (quadratic (Q.1 0) (T.carrierGradient Q 0 (parameter z))).ofLp)
      (carrierSupport z₀ (r := a)) := by
    apply E.continuous.comp_continuousOn
    exact continuousOn_pi.mpr fun i ↦ continuousOn_pi.mpr fun j ↦
      (continuousOn_pi.mp hq i).mul (continuousOn_pi.mp hq j)
  obtain ⟨B, hb⟩ := (carrierSupport_compact z₀ (r := a)).exists_bound_of_continuousOn
    (((hn.pow 2).mul (hn.pow 2)).smul hv)
  exact ⟨max 0 B, le_max_left _ _, fun z hz ↦ (hb z hz).trans (le_max_right _ _)⟩

include hηb hf hInv htrans hcJ haa

/-- The literal original frozen density has a frequency-independent bound
on its actual inverse-input cone. No density bound or integrability is an
assumption (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem exists_retainedFrozenInputDensity_unit_bound :
    ∃ B ≥ (0 : ℝ), ∀ p ∈ frozenInputDomain z₀ ηb r (6 * a),
      ‖inputDensity a₀ J₀ p‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := retainedSeedTensor_bounded T Q F row col Φ Y hP hr har hcarrier
  refine ⟨(‖ηb‖ / cJ) * B, mul_nonneg (div_nonneg (norm_nonneg _) hcJ.le) hB, ?_⟩
  intro p hp
  by_cases hm : angular₀ p.2.1 (‖p.2.2‖⁻¹ • p.2.2) = 0
  · simp only [inputDensity, inputWeight, uncutFrozenCoefficients, hm, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_mul, zero_div, zero_smul, norm_zero]
    positivity
  have hz : p.2.1 ∈ carrierSupport z₀ (r := a) := by
    have hm' := angularMask_nonzero z₀ (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 hm
    exact ⟨closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hm'.1),
      closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hm'.2.1)⟩
  have ha0 := angularMask_mem_Icc z₀ (NormedSpace.normalize ηb) ha'
    (angularWidth_spec hηb hr').1 p.2.1 (‖p.2.2‖⁻¹ • p.2.2)
  have hh0 := FixedCutoffs.highFrequency_mem_Icc ‖p.2.2‖
  have hj := frozenJacobian_pos T Q hP hηb hr har hcarrier hInv htrans hf hcJ hp
  have hq := frozenJacobian_quotient_le T Q hP hηb hr har hcarrier hf hInv htrans hcJ hp
  let w := angular₀ p.2.1 (‖p.2.2‖⁻¹ • p.2.2) ^ 2 *
    FixedCutoffs.highFrequency ‖p.2.2‖ ^ 2 * (‖p.2.2‖ / J₀ p)
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hw : w ≤ ‖ηb‖ / cJ := by
    have ha2 : angular₀ p.2.1 (‖p.2.2‖⁻¹ • p.2.2) ^ 2 ≤ 1 := by nlinarith [ha0.1, ha0.2]
    have hh2 : FixedCutoffs.highFrequency ‖p.2.2‖ ^ 2 ≤ 1 := by nlinarith [hh0.1, hh0.2]
    apply le_trans _ hq
    dsimp [w]
    exact mul_le_of_le_one_left (div_nonneg (norm_nonneg _) hj.le)
      ((mul_le_of_le_one_left (sq_nonneg _) ha2).trans hh2)
  have he : inputDensity a₀ J₀ p = w •
      ((‖normalField T Q F row col Φ Y (fun _ ↦ 1) 0 p.2.1‖ ^ 2 *
          ‖normalField T Q F row col Φ Y (fun _ ↦ 1) 0 p.2.1‖ ^ 2) •
        Matrix.vecMulVec (quadratic (Q.1 0) (T.carrierGradient Q 0 (parameter p.2.1))).ofLp
          (quadratic (Q.1 0) (T.carrierGradient Q 0 (parameter p.2.1))).ofLp) := by
    ext i j
    simp only [inputDensity, inputWeight, uncutFrozenCoefficients, w, Matrix.smul_apply,
      smul_eq_mul, Matrix.vecMulVec_apply]
    ring
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw0]
  exact mul_le_mul hw (hb _ hz) (norm_nonneg _) (div_nonneg (norm_nonneg _) hcJ.le)

/-- Uniform boundedness of the actual zero extension, including points
outside the actual frozen inverse chart (`app:ch_background:prop:bg-frame`). -/
theorem exists_retainedFrozenExtendedDensity_unit_bound :
    ∃ B ≥ (0 : ℝ), ∀ p, ‖extendedDensity a₀ J₀ u₀ Ω₀ p‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_retainedFrozenInputDensity_unit_bound T Q F row col Φ Y hP hηb hr hr' ha' haa
    har hcarrier hf hInv htrans hcJ
  refine ⟨B, hB, fun p ↦ ?_⟩
  by_cases hp : p ∈ Ω₀
  · rw [extendedDensity, indicator_of_mem hp]
    exact hb _ (frozenSymbolInverse_maps T Q hηb hr hInv htrans hp)
  · simpa only [extendedDensity, indicator_of_notMem hp, norm_zero] using hB


end JanetCartan.ContinuumNormal.RetainedFrozen
