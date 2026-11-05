module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.CanonicalGap.PhaseIdentification
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.NormalizedFullPhase.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Construction

/-!
# The same full phase in literal sampling input coordinates

The full-input kernel uses coordinate insertion `fullInputCoordinates`, whereas
the canonical phase chart uses `adaptedSliceCoordinates`. Their composition is
an explicit measure-preserving change of input variables, not a definitional
equality. These identities are consumed by the actual normal-data instantiation
in `app:ch_waves:eq:sampling-operator-bounds`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.RawKernel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison ContinuumRow ContinuumRow.CanonicalConic
open ContinuumRow.CanonicalCarrier
open MeanNormalBound.CanonicalGap MeanNormalBound.NormalizedFullPhase

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The actual change from literal `(s,θ)` insertion to the retained adapted
input chart (`app:ch_waves:eq:sampling-prefix-normal`). -/
def canonicalInputCoordinates : Euclidean (m + 1) ≃ᵐ Euclidean (m + 1) :=
  (fullInputCoordinates m).symm.trans (kernelSliceCoordinates T).symm

/-- The transverse frequency and incidence variable are both unchanged by
the identified chart coordinates (`app:ch_seed:eq:seed-exact-phase-quotient`). -/
@[simp] theorem adapted_canonicalInputCoordinates (u : ℝ × Euclidean m) :
    (adaptedSliceCoordinates T).equiv
      (canonicalInputCoordinates T (fullInputCoordinates m u)) = u := by
  change (adaptedSliceCoordinates T).equiv
    ((adaptedSliceCoordinates T).equiv.symm
      ((fullInputCoordinates m).symm (fullInputCoordinates m u))) = u
  rw [MeasurableEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- The input change preserves literal Lebesgue measure, without a density
factor (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem canonicalInputCoordinates_measurePreserving :
    MeasurePreserving (canonicalInputCoordinates T) volume volume :=
  (kernelSliceCoordinates_measurePreserving T).symm.comp
    (fullInputCoordinates_measurePreserving m).symm

/-- Sampling and the canonical chart use the same three carrier coordinates
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem carrierParameters_eq_sampling (s : ℝ) (v : Euclidean 2) :
    carrierParameters (v, s) = WithLp.toLp 2 (carrierSamplingEquiv (s, v)) := by
  rw [carrierSamplingEquiv_apply]
  ext i
  fin_cases i <;> rfl

variable
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})

/-- The canonical full phase in literal input coordinates equals the actual
integral modulation, retaining its zero endpoint and both spectators
(`app:ch_seed:eq:seed-quotient-integral`). -/
theorem normalizedFullPhase_canonicalInputCoordinates
    (v : Euclidean 2) (ε : ℝ) (x : Euclidean (m + 1)) (u : ℝ × Euclidean m) :
    normalizedFullPhase T Q v ε x
      (canonicalInputCoordinates T (fullInputCoordinates m u)) =
    modulation T Q ((carrierParameters (v, u.1), u.2), ε) (physicalCoordinates T x) := by
  simp only [normalizedFullPhase, adapted_canonicalInputCoordinates]

/-- The common zero endpoint is the original covector differential. It is not
the totalized expression `0 / 0` in the nonzero raw quotient
(`app:ch_seed:eq:seed-quotient-integral`). -/
theorem normalizedFullPhase_canonicalInputCoordinates_zero
    (v : Euclidean 2) (x : Euclidean (m + 1)) (u : ℝ × Euclidean m) :
    normalizedFullPhase T Q v 0 x
      (canonicalInputCoordinates T (fullInputCoordinates m u)) =
    fderiv ℝ (LeadingWave.FullModulation.phase T Q x)
      (T.reference.spatialPatch (carrierParameters (v, u.1))) u.2 := by
  rw [normalizedFullPhase_canonicalInputCoordinates, modulation_zero]
  congr 2
  funext η
  exact current_physicalCoordinates T Q x η

omit Q in
/-- The actual Hamilton constructor closes nonzero phase matching on one
buffer chosen BEFORE the current frame and every dyadic label. No phase
matching hypothesis is assumed (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_rawPhase_canonicalInputCoordinates_radius
    {c C : ℝ} (hP : P.IsValid c C) {M : ℝ} (hM : 0 < M) :
    ∃ e > (0 : ℝ), ∀ Q, ∀ v τ j x (u : ℝ × Euclidean m),
      carrierParameters (v, u.1) ∈ parameterInterior (3 * P.radius / 2) →
      ‖u.2‖ < M → τ * (2 : ℝ) ^ j ∈ Ioo (-e) e → τ ≠ 0 →
      x ∈ ball 0 T.family.radius →
      rawPrimaryPhaseDifference (LeadingWave.FullModulation.phase T Q)
        (T.reference.spatialPatch (carrierParameters (v, u.1))) τ x
          ((2 : ℝ) ^ j • u.2) =
      (2 : ℝ) ^ j * normalizedFullPhase T Q v (τ * (2 : ℝ) ^ j) x
        (canonicalInputCoordinates T (fullInputCoordinates m u)) := by
  obtain ⟨e, he, hphase⟩ := exists_normalizedFullPhase_quotient_radius T hP hM
  refine ⟨e, he, ?_⟩
  intro Q v τ j x u hz hu hε hτ hx
  rw [RawInputDilation.rawPrimaryPhaseDifference_dilate _ _ hτ (by positivity)]
  congr 1
  have h := hphase Q v (τ * (2 : ℝ) ^ j) x
    (canonicalInputCoordinates T (fullInputCoordinates m u))
    (by simpa only [adapted_canonicalInputCoordinates] using hz)
    (by simpa only [adapted_canonicalInputCoordinates] using hu) hε
    (mul_ne_zero hτ (by positivity)) hx
  simpa only [adapted_canonicalInputCoordinates, rawPrimaryPhaseDifference,
    LeadingWave.FullModulation.phase, ActualCarriers.carrierPhase, spatialCarrier, id_eq] using h.symm

end JanetCartan.Sampling.RawKernel
