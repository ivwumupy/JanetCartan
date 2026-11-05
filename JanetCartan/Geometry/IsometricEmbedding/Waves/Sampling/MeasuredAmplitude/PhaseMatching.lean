module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.KernelConstruction

/-!
# The actual retained phase on the nonzero measured kernel

The literal Hamilton quotient and its canonical integral homotopy agree on
one fixed buffer before the current frame, history and bands. The explicit
raw phase/carrier extensions disappear on the measured support. Off that
support the amplitude is zero, so no global equality of unrelated extensions
is required. This closes the phase input of the actual column/normal bridge
for `app:ch_waves:eq:sampling-prefix-normal`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation RawKernel
open SamplingKernelBounds RawPrimary.MaskProfiles RawInputPartition FullPhaseCharts
open MeanNormalBound.NormalizedFullPhase MeanNormalBound.CanonicalGap ContinuumRow
open FullNormalGeometry.PhaseJets

variable {m N J p : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
    Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)
  (measurement : Euclidean (m + 1) →
    Matrix (Fin N) (Fin (m + 1)) ℂ →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
  (χ : Euclidean (m + 1) → ℝ)
  (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  {ρ : ℝ} (hρ : 0 < ρ)
  {c C : ℝ} (hP : P.IsValid c C)
  (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  (hs : ContDiff ℝ ∞ (fun q : ℝ × (Euclidean (m + 1) ×
    (Euclidean 3 × Euclidean (m + 1 - 1))) ↦
      supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ
        q.1 q.2.2.1 q.2.1 q.2.2.2))
  (M : ℝ) (hM : 0 ≤ M)
  (hb : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x ξ,
    ‖supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ
      τ z x ξ‖ ≤ M)
  (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
  (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
  (hH : ContDiff ℝ ∞ highPass) (hH₀ : ∀ η, ‖η‖ ≤ 1 → highPass η = 0)
  (B : ℝ) (hB : 0 ≤ B) (hdB : ∀ η, ‖detectorMask angular highPass η‖ ≤ B)
  (τ : (Fin 3 → Fin (p + 1)) → ℝ)
  (hτ : ∀ color, τ color ∈ Icc (-1 : ℝ) 1) (hτ₀ : ∀ color, τ color ≠ 0)

/-- One positive phase buffer fixed before the current frame, measured
coefficients, bands and colors (`app:ch_waves:setup:oscillatory`). -/
def measuredPhaseRadius : ℝ :=
  min ((exists_rawPhase_canonicalInputCoordinates_radius T hP
    (M := 3) (by norm_num)).choose / 2) (ρ / 8)

include hρ in
/-- Positivity of the common actual-kernel phase buffer
(`app:ch_waves:setup:oscillatory`). -/
theorem measuredPhaseRadius_pos : 0 < measuredPhaseRadius T hP (ρ := ρ) := by
  have he := (exists_rawPhase_canonicalInputCoordinates_radius T hP
    (M := 3) (by norm_num)).choose_spec.1
  exact lt_min (by linarith) (by positivity)

/-- Every nonzero measured coefficient retains the original physical and
carrier supports and the complete normalized wide band, including its
high-pass transition (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem supportedMeasuredNormalAmplitude_nonzero
    (ψ : SeparatedSampling.Point → ℝ) (j : ℕ) (v : Euclidean 2)
    (ε : ℝ) (x : Euclidean (m + 1)) (s : ℝ) (θ : Euclidean (m + 1 - 1))
    (hn : supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
      angular highPass ψ j v ε x (fullInputCoordinates m (s, θ)) ≠ 0) :
    χ x ≠ 0 ∧ ψ (carrierSamplingEquiv (s, v)) ≠ 0 ∧
      1 / 2 < ‖θ‖ ∧ ‖θ‖ < 2 := by
  simp only [supportedMeasuredNormalAmplitude, normalizedMeasuredPullback,
    normalizedRetainedMask, normalizedRetainedPoint, inputCoordinates_apply,
    adapted_canonicalInputCoordinates] at hn
  have hm : normalizedMask (n := m + 1) angular highPass j θ ≠ 0 := by
    intro hz
    exact hn (by simp only [hz, mul_zero, zero_smul])
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hz
    exact hn (by simp only [fullMeasuredDerivativePolynomial, hz, Complex.ofReal_zero,
      zero_smul, smul_zero])
  · intro hz
    exact hn (by simp only [hz, Complex.ofReal_zero, zero_mul, zero_smul])
  · exact lt_of_not_ge (fun hh ↦ hm
      (normalizedMask_eq_zero_of_le (n := m + 1) angular highPass j hh))
  · exact lt_of_not_ge (fun hh ↦ hm
      (normalizedMask_eq_zero_of_ge (n := m + 1) angular highPass j hh))

/-- The actual measured homotopy vanishes off the original full-input
restriction. This is derived from the smooth radial mask and the literal
carrier coordinate, not assumed as an operator-support field
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem supportedMeasuredNormalAmplitude_eq_zero_off_fullInputDomain
    (ψ : SeparatedSampling.Point → ℝ) {R Pψ : ℝ}
    (hψ : SeparatedSampling.PatchBounds ψ R Pψ)
    (j : ℕ) (v : Euclidean 2) (ε : ℝ) (u : Euclidean (m + 1))
    (hu : u ∉ fullInputDomain m 0 R) (x : Euclidean (m + 1)) :
    supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
      angular highPass ψ j v ε x u = 0 := by
  obtain ⟨⟨s, θ⟩, rfl⟩ := (fullInputCoordinates m).surjective u
  by_contra hn
  obtain ⟨_, hψ₀, hlo, hhi⟩ := supportedMeasuredNormalAmplitude_nonzero
    T Q F row col Φ Y r measurement χ a hρ angular highPass ψ j v ε x s θ hn
  apply hu
  rw [fullInputCoordinates_mem_domain]
  refine ⟨?_, ?_⟩
  · have hh := hψ.support _ hψ₀ 0
    change |s| ≤ R at hh
    exact abs_le.mp hh
  · constructor
    · norm_num only [dyadicScale, pow_zero, one_div, mem_closedBall, dist_zero_right]
      exact hhi.le
    · simpa only [dyadicScale, pow_zero, one_div, mem_ball,
        dist_zero_right, not_lt] using hlo.le

local notation "D" => retainedMeasuredKernelData (J := J) T Q F row col Φ Y r measurement χ
  a hρ hP hcarrier hs M hM hb angular highPass ha hH hH₀ B hB hdB τ hτ hτ₀

/-- On every nonzero measured coefficient, the SAME constructed kernel
has exactly the full canonical phase after literal input dilation. The
phase and carrier extensions are removed using their actual plateaus.
The buffer depends only on the retained chart and cell, before all varying
data (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem retainedMeasuredKernelData_phase_on_support
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (ψ : SeparatedSampling.Point → ℝ)
    (hψgraph : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
        closedBall a.2 (ρ / 4))
    (hψchart : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      carrierParameters (v, s) ∈ parameterInterior (3 * P.radius / 2))
    (j : Fin J) (color : Fin 3 → Fin (p + 1)) (v : Euclidean 2)
    (hscale : |τ color| * (2 : ℝ) ^ j.val ≤ measuredPhaseRadius T hP (ρ := ρ))
    (s : ℝ) (θ : Euclidean (m + 1 - 1)) (x : Euclidean (m + 1))
    (hn : supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
      angular highPass ψ j.val v ((τ color) * (2 : ℝ) ^ j.val) x
        (fullInputCoordinates m (s, θ)) ≠ 0) :
    (D).phase (((j, (color, carrierSamplingEquiv (s, v))),
      (2 : ℝ) ^ j.val • θ), x) =
      (2 : ℝ) ^ j.val * normalizedFullPhase T Q v ((τ color) * (2 : ℝ) ^ j.val) x
        (canonicalInputCoordinates T (fullInputCoordinates m (s, θ))) := by
  obtain ⟨hx, hz, _, hθ⟩ := supportedMeasuredNormalAmplitude_nonzero
    T Q F row col Φ Y r measurement χ a hρ angular highPass ψ
      j.val v ((τ color) * (2 : ℝ) ^ j.val) x s θ hn
  have hzg := hψgraph s v hz
  have hzc : carrierParameters (v, s) ∈ closedBall a.2.1 ρ := by
    rw [← closedBall_prod_same] at hzg
    exact closedBall_subset_closedBall (by linarith) hzg.1
  change rawPrimaryPhaseDifference (extendedRetainedPhase T Q)
    (extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 (carrierSamplingEquiv (s, v))))
    (τ color) x ((2 : ℝ) ^ j.val • θ) = _
  rw [← carrierParameters_eq_sampling, extendedRetainedCarrier_eq T a.2.1 hρ hzc]
  have hd : ‖(τ color) • ((2 : ℝ) ^ j.val • θ)‖ ≤ ρ / 4 := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j.val), ← mul_assoc]
    have hh := hscale.trans (min_le_right _ _)
    exact (mul_le_mul hh hθ.le (norm_nonneg _) (by positivity)).trans_eq (by ring)
  rw [extendedRetainedPhase_difference_eq T Q a hρ hphase (hχ hx) hzg
    (τ color) ((2 : ℝ) ^ j.val • θ) hd]
  have hxb : x ∈ ball 0 T.family.radius := by
    have hh := hphase (closedBall_subset_closedBall (by linarith : ρ / 2 ≤ 2 * ρ)
      (retained_shift_mem_plateau T a (hχ hx) hzg (d := 0) (by simp; positivity)))
    change (x, T.reference.spatialPatch (carrierParameters (v, s)) + 0) ∈
      ball (0, FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius at hh
    rw [← ball_prod_same] at hh
    exact hh.1
  apply (exists_rawPhase_canonicalInputCoordinates_radius T hP
    (M := 3) (by norm_num)).choose_spec.2 Q v (τ color) j.val x (s, θ)
      (hψchart s v hz) (by linarith) _ (hτ₀ color) hxb
  apply abs_lt.mp
  rw [abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j.val)]
  have he := (exists_rawPhase_canonicalInputCoordinates_radius T hP
    (M := 3) (by norm_num)).choose_spec.1
  exact hscale.trans_lt ((min_le_left _ _).trans_lt (by linarith))

end JanetCartan.Sampling.MeasuredAmplitude
