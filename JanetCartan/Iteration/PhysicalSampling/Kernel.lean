module

public import JanetCartan.Iteration.PhysicalSampling.NormalData
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.PhaseMatching

/-!
# The actual scalar kernel on the retained current phase

Use the original retained phase and carrier extensions, the same colored inverse
frequencies and the original angular/high-pass mask. The fixed physical scalar
cutoff replaces the stress amplitude; no measurement is inverted. On its actual
support the phase is exactly the original canonical full phase, with the literal
dyadic normalization. Consumer: the scalar continuum normal and common event in
`new:eq:amplitude-test`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalSampling

open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation
open FullPhaseCharts Sampling Sampling.RawKernel Sampling.MeasuredAmplitude
open Sampling.MeanNormalBound.NormalizedFullPhase Sampling.MeanNormalBound.CanonicalGap
open Sampling.FullNormalGeometry Sampling.FullNormalGeometry.PhaseJets
open SamplingKernelBounds RawPrimary.MaskProfiles RawInputPartition PhysicalMean ContinuumRow

variable {m J p : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (χ : ContDiffBump (0 : Euclidean (m + 1)))
  (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  {ρ : ℝ} (hρ : 0 < ρ) {c C : ℝ} (hP : P.IsValid c C)
  (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ)
  (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
  (hH : ContDiff ℝ ∞ H) (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0)
  (B : ℝ) (hB : 0 ≤ B) (hdB : ∀ η, ‖detectorMask angular H η‖ ≤ B)
  (τ : (Fin 3 → Fin (p + 1)) → ℝ) (hτ₀ : ∀ color, τ color ≠ 0)

/-- The scalar auxiliary kernel for the SAME current retained phase, colors,
carrier labels and input partition (`new:eq:amplitude-test`). -/
def retainedScalarKernelData :
    BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × SeparatedSampling.Point)) (m + 1) :=
  scalarAuxiliaryKernel (by omega) χ
    (fun _ : (Fin 3 → Fin (p + 1)) × SeparatedSampling.Point ↦ extendedRetainedPhase T Q)
    (fun q ↦ extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 q.2))
    (fun q ↦ τ q.1) (detectorMask angular H)
    ((contDiff_extendedRetainedPhase T Q).continuous.comp
      (f := fun q : (((Fin 3 → Fin (p + 1)) × SeparatedSampling.Point) ×
        Euclidean (m + 1)) × Euclidean (m + 1 - 1) ↦ (q.1.2, q.2)) (by fun_prop))
    ((contDiff_extendedRetainedCarrier T hP a.2.1 hρ hcarrier).continuous.comp (by fun_prop))
    (by fun_prop) (fun q ↦ hτ₀ q.1)
    (contDiff_detectorMask angular H ha hH hH₀).continuous hB hdB

local notation "D" => retainedScalarKernelData (J := J) T Q χ a hρ hP hcarrier
  angular H ha hH hH₀ B hB hdB τ hτ₀

/-- The squared-kernel constant depends only on the fixed scalar cutoff and
original detector, not on the current phase, frequencies, colors or ceiling. -/
theorem retainedScalarKernelData_squaredKernelConstant :
    (D).squaredKernelConstant = volume.real (tsupport (χ : Euclidean (m + 1) → ℝ)) *
      B ^ 2 * ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2)) ^ 2 *
        RawInputRealization.unitBallVolume (m + 1) := by
  simp only [retainedScalarKernelData, scalarAuxiliaryKernel,
    BandKernelData.squaredKernelConstant, bandKernelData, mul_one]

/-- Literal physical scalar kernel, including the unchanged Fourier scalar,
half derivative, smooth radial band, angular detector and high-pass. -/
theorem retainedScalarKernelData_kernel (j : Fin J)
    (color : Fin 3 → Fin (p + 1)) (z : SeparatedSampling.Point)
    (x : Euclidean (m + 1)) (η : Euclidean (m + 1 - 1)) :
    (D).kernel (j, (color, z)) η x =
      ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) : ℝ) •
        ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand (detectorMask angular H) j.val η) •
          (Complex.exp (Complex.I * (rawPrimaryPhaseDifference (extendedRetainedPhase T Q)
            (extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 z)) (τ color) x η : ℂ)) •
              scalarAuxiliaryAmplitude (by omega) χ () x 0) := by
  unfold retainedScalarKernelData scalarAuxiliaryKernel
  apply bandKernelData_kernel

/-- Remove the phase extensions on the actual scalar amplitude support. The
same canonical phase is retained; no measured-row norm is used. -/
theorem retainedScalarKernelData_phase_on_support
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (hχ : Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall a.1 (ρ / 2))
    (ψ : SeparatedSampling.Point → ℝ)
    (hψgraph : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
        closedBall a.2 (ρ / 4))
    (hψchart : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      carrierParameters (v, s) ∈ parameterInterior (3 * P.radius / 2))
    (j : Fin J) (color : Fin 3 → Fin (p + 1)) (v : Euclidean 2)
    (hscale : |τ color| * (2 : ℝ) ^ j.val ≤ measuredPhaseRadius T hP (ρ := ρ))
    (s : ℝ) (θ : Euclidean (m + 1 - 1)) (x : Euclidean (m + 1))
    (hn : scalarNormalizedAmplitude T χ ψ angular H j.val
      ((τ color) * (2 : ℝ) ^ j.val, v, x, fullInputCoordinates m (s, θ)) ≠ 0) :
    (D).phase (((j, (color, carrierSamplingEquiv (s, v))), (2 : ℝ) ^ j.val • θ), x) =
      (2 : ℝ) ^ j.val * normalizedFullPhase T Q v ((τ color) * (2 : ℝ) ^ j.val) x
        (canonicalInputCoordinates T (fullInputCoordinates m (s, θ))) := by
  obtain ⟨hx, hz, _, hθ⟩ := scalarNormalizedAmplitude_nonzero
    T χ ψ angular H j.val ((τ color) * (2 : ℝ) ^ j.val) v x s θ hn
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

end JanetCartan.PhysicalSampling
