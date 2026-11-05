module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.CorrectedSamplingMean.Literal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.PhaseMatching

/-!
# Literal corrected band normalization

Identify the supplied canonical sampling kernel with the normal homotopy at
`ε = τ * 2^j`. Both corrected factors keep their same fixed physical rate.
The original Fourier constant and half derivative are kept exactly.
Consumer: `app:ch_waves:eq:sampling-operator-bounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option quotPrecheck false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedMean
open CanonicalRowComparison CanonicalAtomRealization CorrectedAtoms
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open MeasuredAmplitude FullNormalGeometry FullNormalGeometry.PhaseJets FullPhaseCharts
open MeanNormalBound.NormalizedFullPhase ContinuumRow RawPrimary.MaskProfiles
open MeanNormalBound.CanonicalGap
open RawKernel RawInputPartition FullPhaseCharts.ActualComparison

variable {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
    Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  (χ : Euclidean (m + 1) → ℝ)
  (B : MetricField (m + 1) →ₗ[ℝ] (Euclidean (m + 1) → Euclidean N))
  (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)
  (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
  (C : Euclidean (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ →L[ℝ]
    Euclidean (m + 1))
  (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)

variable {p J : ℕ}
  (hκc : HasCompactSupport κ) (rate : (Fin 3 → Fin (p + 1)) → ℝ)
  (hA : ∀ color, Continuous (fun w ↦ κ w •
    fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate color) w))
  (hC : Continuous C) {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
  (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  (hrate : ∀ color, rate color ≠ 0)
  (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
  (hd : Continuous (detectorMask angular highPass))
  (Md : ℝ) (hMd : 0 ≤ Md) (hdb : ∀ η, ‖detectorMask angular highPass η‖ ≤ Md)

local notation "D" => correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC
  Prod.fst continuous_fst (fun q ↦ WithLp.toLp 2 q.2) (by fun_prop) hP z₀ hρ hcarrier hrate
  (detectorMask angular highPass) hd Md hMd hdb J

/-- The SAME corrected band amplitude matches the fixed-rate normal homotopy
with the transverse Jacobian, half derivative and Fourier scalar unchanged.
Only the existing carrier plateau is used; no frequency dependence of the
response solver is differentiated (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem correctedColoredCrossBandData_amplitude_eq_fixedRateNormal
    (ψ : SeparatedSampling.Point → ℝ)
    (hψ : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      carrierParameters (v, s) ∈ closedBall z₀ ρ)
    (j : Fin J) (color : Fin 3 → Fin (p + 1)) (v : Euclidean 2)
    (s : ℝ) (θ : Euclidean (m + 1 - 1)) (x : Euclidean (m + 1)) (i : Fin (m + 1)) :
    (Real.sqrt (((2 : ℝ) ^ j.val) ^ m) : ℂ) *
      (ψ (carrierSamplingEquiv (s, v)) : ℂ) *
      (Real.sqrt ‖(2 : ℝ) ^ j.val • θ‖ : ℂ) * (D).mask ((2 : ℝ) ^ j.val • θ) *
      (D).amplitude (((j, (color, carrierSamplingEquiv (s, v))),
        (2 : ℝ) ^ j.val • θ), x) i =
      (NormalComparison.normalOperatorScale (m + 1) ((2 : ℝ) ^ j.val) : ℂ) *
        fixedRateNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ (rate color)
          angular highPass ψ j.val v (rate color * (2 : ℝ) ^ j.val) x
            (fullInputCoordinates m (s, θ)) i := by
  rw [fixedRateNormalAmplitude_literal]
  by_cases hz : ψ (carrierSamplingEquiv (s, v)) = 0
  · simp only [hz, Complex.ofReal_zero, mul_zero, zero_mul, zero_smul, PiLp.zero_apply]
  change (Real.sqrt (((2 : ℝ) ^ j.val) ^ m) : ℂ) * _ * _ *
      detectorMask angular highPass _ *
        measuredBandAmplitude
          (fun q : (Fin 3 → Fin (p + 1)) × SeparatedSampling.Point ↦
            fun x ξ ↦ fixedRateCrossCoefficient T Q F row col Φ Y χ B r κ C z₀ hρ
              (rate q.1) (x, WithLp.toLp 2 q.2, ξ))
          (fun q ↦ extendedRetainedCarrier T z₀ hρ (WithLp.toLp 2 q.2))
          (fun q ↦ rate q.1)
          (((j, (color, carrierSamplingEquiv (s, v))), (2 : ℝ) ^ j.val • θ), x) i = _
  have hn := measuredBandAmplitude_normalization (by omega : 1 ≤ m + 1)
    (fun q : (Fin 3 → Fin (p + 1)) × SeparatedSampling.Point ↦
      fun x ξ ↦ fixedRateCrossCoefficient T Q F row col Φ Y χ B r κ C z₀ hρ
        (rate q.1) (x, WithLp.toLp 2 q.2, ξ))
    (fun q ↦ extendedRetainedCarrier T z₀ hρ (WithLp.toLp 2 q.2))
    (fun q ↦ rate q.1) (detectorMask angular highPass) j
    (color, carrierSamplingEquiv (s, v)) (ψ (carrierSamplingEquiv (s, v))) x θ i
  simp only [Nat.add_sub_cancel] at hn
  rw [hn]
  simp only [normalizedMeasuredAmplitude, normalizedMask, PiLp.smul_apply, smul_eq_mul,
    ← carrierParameters_eq_sampling, extendedRetainedCarrier_eq T z₀ hρ (hψ s v hz)]
  congr 1
  ring

/-- On its nonzero coefficient the corrected kernel has the original full
canonical phase. The supplied cutoff and carrier plateau discharge the local
extension identities; no global chart assumption is imposed at spectators
outside the retained chart (`app:ch_waves:eq:phase-quotient`). -/
theorem correctedColoredCrossBandData_phase_on_fixedRateNormal_support
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
    (haz : a.2.1 = z₀) (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (hκ : Prod.fst '' Function.support κ ⊆ closedBall a.1 (ρ / 2))
    (ψ : SeparatedSampling.Point → ℝ)
    (hψgraph : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
        closedBall a.2 (ρ / 4))
    (hψchart : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      carrierParameters (v, s) ∈ parameterInterior (3 * P.radius / 2))
    (j : Fin J) (color : Fin 3 → Fin (p + 1)) (v : Euclidean 2)
    (hscale : |rate color| * (2 : ℝ) ^ j.val ≤ measuredPhaseRadius T hP (ρ := ρ))
    (s : ℝ) (θ : Euclidean (m + 1 - 1)) (x : Euclidean (m + 1))
    (hn : fixedRateNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ (rate color)
      angular highPass ψ j.val v (rate color * (2 : ℝ) ^ j.val) x
        (fullInputCoordinates m (s, θ)) ≠ 0) :
    (D).phase (((j, (color, carrierSamplingEquiv (s, v))), (2 : ℝ) ^ j.val • θ), x) =
      (2 : ℝ) ^ j.val * normalizedFullPhase T Q v (rate color * (2 : ℝ) ^ j.val) x
        (canonicalInputCoordinates T (fullInputCoordinates m (s, θ))) := by
  obtain ⟨hx, hz, _, hθ⟩ := fixedRateNormalAmplitude_nonzero
    T Q F row col Φ Y χ B r κ C z₀ hρ (rate color) angular highPass ψ
      j.val v (rate color * (2 : ℝ) ^ j.val) x s θ hn
  have hzg := hψgraph s v hz
  have hzc : carrierParameters (v, s) ∈ closedBall z₀ ρ := by
    rw [← closedBall_prod_same] at hzg
    rw [← haz]
    exact closedBall_subset_closedBall (by linarith) hzg.1
  change rawPrimaryPhaseDifference (extendedRetainedPhase T Q)
    (extendedRetainedCarrier T z₀ hρ (WithLp.toLp 2 (carrierSamplingEquiv (s, v))))
    (rate color) x ((2 : ℝ) ^ j.val • θ) = _
  rw [← carrierParameters_eq_sampling, extendedRetainedCarrier_eq T z₀ hρ hzc]
  have hdshift : ‖(rate color) • ((2 : ℝ) ^ j.val • θ)‖ ≤ ρ / 4 := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j.val), ← mul_assoc]
    have hh := hscale.trans (min_le_right _ _)
    exact (mul_le_mul hh hθ.le (norm_nonneg _) (by positivity)).trans_eq (by ring)
  rw [extendedRetainedPhase_difference_eq T Q a hρ hphase (hκ hx) hzg
    (rate color) ((2 : ℝ) ^ j.val • θ) hdshift]
  have hxb : x ∈ ball 0 T.family.radius := by
    have hh := hphase (closedBall_subset_closedBall (by linarith : ρ / 2 ≤ 2 * ρ)
      (retained_shift_mem_plateau T a (hκ hx) hzg (d := 0) (by simp; positivity)))
    change (x, T.reference.spatialPatch (carrierParameters (v, s)) + 0) ∈
      ball (0, FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius at hh
    rw [← ball_prod_same] at hh
    exact hh.1
  apply (exists_rawPhase_canonicalInputCoordinates_radius T hP
    (M := 3) (by norm_num)).choose_spec.2 Q v (rate color) j.val x (s, θ)
      (hψchart s v hz) (by linarith) _ (hrate color) hxb
  apply abs_lt.mp
  rw [abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j.val)]
  have he := (exists_rawPhase_canonicalInputCoordinates_radius T hP
    (M := 3) (by norm_num)).choose_spec.1
  exact hscale.trans_lt ((min_le_left _ _).trans_lt (by linarith))

end JanetCartan.Sampling.CorrectedMean
