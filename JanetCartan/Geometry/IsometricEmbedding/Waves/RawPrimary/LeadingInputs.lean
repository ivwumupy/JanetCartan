module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.JointRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.MinorFromDenominator

/-!
# Raw correction from the retained leading-family conclusions

For `app:ch_waves:eq:primary-algebraic-correction`, use the SAME scalar,
nullvectors and reduced transport identity exported by the actual finite
leading family. The selected minor is derived from its two nonzero
nullvectors. The reduced transport identity already supplies solvability;
there is no need to reconstruct it from a separate denominator hypothesis.
The raw-primary parent still instantiates these outputs on its common family
and supplies quantitative coefficient and slice bounds.
-/

@[expose] public noncomputable section

open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open LeadingWave.FullModulation NullTransport ActualCarriers FrozenMenu CurrentFullPhase

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- The actual leading theorem's nonzero nullvectors and reduced transport
equation imply cancellation for the literal orthogonal correction. No selected
minor or transport-denominator premise is added to those retained outputs
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullCorrectionCovector_cancel_of_leading_outputs
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : (w.1, w.2.2) ∈ phaseDomain T)
    (hk : nullvector T Q col w ≠ 0) (hl : conullvector T Q row w ≠ 0)
    (htransport : conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
      (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2) •
        nullvector T Q col (x, w.2)) w.1 = 0) :
    Complex.I • ((reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).map
      Complex.ofReal *ᵥ (fun j ↦ fullCorrectionCovector T Q F row col Φ Y r w j)) +
      (fun i ↦ (reducedOperator F Q.1
        (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1 i : ℂ)) = 0 := by
  have hm := fullPhase_minor_ne_zero_of_nullvectors T Q row col hw hk hl
  simpa only [fullCorrectionCovector, fullLeadingCovector, PiLp.smul_apply, euclideanComplexInclusion_apply,
    PiLp.toLp_apply, Pi.smul_def] using orthogonalSymbolInverse_complex_cancel
      (H := reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2))
      (phase_characteristic T Q hw) hm htransport

/-- Joint regularity of the SAME raw correction follows directly from the
actual leading family's scalar regularity and two nonvanishing conclusions,
without a new minor neighborhood (`app:ch_waves:thm:wkb`). -/
theorem contDiffOn_fullCorrectionCovector_of_leading_outputs
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (himm : IsImmersionOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) :
    ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) Ω :=
  contDiffOn_fullCorrectionCovector T Q F row col Φ Y r hΩ hspace hphase hF himm
    (fun w hw ↦ fullPhase_minor_ne_zero_of_nullvectors T Q row col (hphase w hw)
      (hnonzero w hw).1 (hnonzero w hw).2) hα

end JanetCartan.RawPrimary
