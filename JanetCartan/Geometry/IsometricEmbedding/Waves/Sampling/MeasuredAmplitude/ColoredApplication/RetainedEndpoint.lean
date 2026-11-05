module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.FullNormalData
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColoredApplication.InputCoordinates

/-!
# Actual zero phase and principal amplitude of the retained family

Consume the literal field equalities returned by
`exists_full_retained_measuredKernel_mean`. The zero endpoint is the canonical
phase differential and the actual leading principal polynomial of that SAME
family. The auxiliary smooth carrier cutoff equals one on the original patch
support; it is not identified with the patch weight. These are the primitive
endpoint identities for `app:ch_waves:eq:colored-normal-comparison`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation RawKernel
open NormalComparison MeanNormalBound.NormalizedFullPhase MeanNormalBound.CanonicalGap
open ContinuumRow RawPrimary.MaskProfiles FullPhaseCharts

variable {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (Metric.closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean m × (Euclidean 3 × Euclidean m)) →
    Euclidean m × (Euclidean 3 × Euclidean m))
  (r : Euclidean m × Euclidean 3 → ℝ)
  (measurement : Euclidean (m + 1) →
    Matrix (Fin N) (Fin (m + 1)) ℂ →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
  (χ : Euclidean (m + 1) → ℝ)
  (angular : Euclidean m → ℂ) (H : Euclidean m → ℝ)
  (ψ : SeparatedSampling.Point → ℝ)
  {G : UniformNormalGeometry (m + 1) (m + 1)} {C : ℕ → ℝ}
  (Ns : ℕ → UniformNormalData G C) (v : Euclidean 2)

/-- The actual normal family has the canonical transport phase, derived from
the integral homotopy at zero. This is not the totalized nonzero quotient
evaluated at zero (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem retainedNormal_zero_phase
    (hphase : ∀ j, (Ns j).phase = fun ε x u ↦
      normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))
    (j : ℕ) (x : Euclidean (m + 1)) (u : ℝ × Euclidean m) :
    (Ns j).phase 0 x (fullInputCoordinates m u) =
      fderiv ℝ (LeadingWave.FullModulation.phase T Q x)
        (T.reference.spatialPatch (carrierParameters (v, u.1))) u.2 := by
  rw [hphase j]
  exact normalizedFullPhase_canonicalInputCoordinates_zero T Q v x u

/-- The actual amplitude endpoint is the original measured leading principal
matrix, with every detector and carrier cutoff retained. Its literal field
identity is one of the outputs of `exists_full_retained_measuredKernel_mean`
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem retainedNormal_zero_amplitude
    (hamp : ∀ j, ∀ ε ∈ Icc 0 G.ε₀, ∀ x u,
      (Ns j).amplitude ε x u =
        (fullMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ
          (detectorMask (n := m + 1) angular H) ψ j v ε x
            (canonicalInputCoordinates T u)).ofLp)
    (j : ℕ) (x : Euclidean (m + 1)) (u : ℝ × Euclidean m) :
    (Ns j).amplitude 0 x (fullInputCoordinates m u) =
      (((ψ (carrierSamplingEquiv (u.1, v)) : ℂ) *
        normalizedMask (n := m + 1) angular H j u.2) •
        ((χ x : ℂ) • measurement x
          (RawPrimary.fullLeadingPrincipalMatrix T Q F row col Φ Y r
            (x, (carrierParameters (v, u.1),
              T.reference.spatialPatch (carrierParameters (v, u.1))))))).ofLp := by
  rw [hamp j 0 ⟨le_rfl, G.ε₀_pos.le⟩,
    fullMeasuredNormalAmplitude_literal_zero]

/-- Multiplying the actual zero amplitude by the ORIGINAL patch weight
removes only the auxiliary carrier cutoff, using its proved plateau. This
identity requires neither a smooth square root of the patch weight nor a
rectangular phase domain (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem patch_mul_retainedNormal_zero_amplitude
    (hamp : ∀ j, ∀ ε ∈ Icc 0 G.ε₀, ∀ x u,
      (Ns j).amplitude ε x u =
        (fullMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ
          (detectorMask (n := m + 1) angular H) ψ j v ε x
            (canonicalInputCoordinates T u)).ofLp)
    (φ : SeparatedSampling.Point → ℝ) (hplateau : ∀ z, φ z ≠ 0 → ψ z = 1)
    (j : ℕ) (x : Euclidean (m + 1)) (u : ℝ × Euclidean m) (i : Fin (m + 1)) :
    (φ (carrierSamplingEquiv (u.1, v)) : ℂ) *
        (Ns j).amplitude 0 x (fullInputCoordinates m u) i =
      (φ (carrierSamplingEquiv (u.1, v)) : ℂ) *
        normalizedMask (n := m + 1) angular H j u.2 *
          (((χ x : ℂ) • measurement x
            (RawPrimary.fullLeadingPrincipalMatrix T Q F row col Φ Y r
              (x, (carrierParameters (v, u.1),
                T.reference.spatialPatch (carrierParameters (v, u.1)))))) i) := by
  rw [retainedNormal_zero_amplitude T Q F row col Φ Y r measurement χ angular H ψ Ns v hamp]
  by_cases hz : φ (carrierSamplingEquiv (u.1, v)) = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul]
  · rw [hplateau _ hz]
    simp only [Complex.ofReal_one, one_mul, PiLp.smul_apply, smul_eq_mul]
    ring

end JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
