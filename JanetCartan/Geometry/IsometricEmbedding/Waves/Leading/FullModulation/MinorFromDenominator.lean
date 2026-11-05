module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.Construction

/-!
# Recovering the selected minor from the actual transport denominator

The full-modulation construction retains nonzero selected left and right
nullvectors on its common domain. These already force the SAME selected
adjugate entry to be nonzero on the characteristic set. The transport
denominator supplies these nonvanishing facts at the earlier construction
stage. The consumers are the smooth orthogonal
inverse and correction in `RawPrimary.Correction.JointRegularity`, for
`app:ch_waves:eq:primary-algebraic-correction`. No new minor neighborhood is
needed for these regularity assertions. Quantitative correction estimates
still require a uniform numerical bound on the reciprocal minor.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.LeadingWave.FullModulation

open NullTransport ActualCarriers FrozenMenu CurrentFullPhase

private theorem selected_minor_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.det = 0) {r c : ι}
    (hk : rightNullvector A c ≠ 0) (hl : leftNullvector A r ≠ 0) :
    A.adjugate r c ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, A.adjugate r j ≠ 0 := by
    by_contra! h
    apply hl
    funext j
    exact h j
  intro hrc
  apply hk
  have h := kernel_eq_smul_rightNullvector hA hj (mulVec_rightNullvector hA c)
  simpa only [rightNullvector, hrc, zero_div, zero_smul] using h

/-- The two nonvanishing conclusions retained by
`exists_finite_actual_leading_family` imply nonvanishing of the SAME selected
minor. This supplies the raw correction's joint-regularity input directly
from the final leading-family output
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullPhase_minor_ne_zero_of_nullvectors {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (row col : Fin n) {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : (w.1, w.2.2) ∈ phaseDomain T)
    (hk : nullvector T Q col w ≠ 0) (hl : conullvector T Q row w ≠ 0) :
    (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col ≠ 0 := by
  apply selected_minor_ne_zero (phase_characteristic T Q hw) ?_ hl
  intro hz
  apply hk
  ext j
  exact congrFun hz j

/-- The denominator already retained by the actual leading family supplies
the fixed-entry nonvanishing input of `RawPrimary.contDiffOn_fullSymbolInverse`
and `RawPrimary.contDiffOn_fullCorrectionCovector`. The characteristic equation
comes from the SAME full phase (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullPhase_minor_ne_zero_of_denominator {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (row col : Fin n) {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : (w.1, w.2.2) ∈ phaseDomain T)
    (hd : adaptedDenominator T Q row col w ≠ 0) :
    (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col ≠ 0 := by
  obtain ⟨hk, hl⟩ := nullvectors_ne_zero_of_denominator T Q row col w hd
  exact fullPhase_minor_ne_zero_of_nullvectors T Q row col hw hk hl

end JanetCartan.LeadingWave.FullModulation
