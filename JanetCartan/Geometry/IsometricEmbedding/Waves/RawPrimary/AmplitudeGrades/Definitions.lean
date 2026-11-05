module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.FullRegularity

/-!
# The same full primary derivative amplitude

These names specialize the canonical formulas to the phase, leading covector,
and correction already used by `fullPrimaryWave`. They are shared by the
quantitative reconstruction and polynomial deductions for
`app:ch_waves:eq:WKB-amplitude-difference`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseTransfer AmbientResponse

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- The literal derivative amplitude for the SAME atom; this is precisely
the specialization in `fullPrimaryWave_derivative_representation`, with the
Frobenius norm (`app:ch_waves:eq:WKB-amplitude-difference`). -/
def fullDerivativeAmplitude (τ : ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : Matrix (Fin N) (Fin n) ℂ :=
  canonicalDerivativeAmplitude F τ (fun p ↦ phase T Q p.1 p.2)
    (fun p ↦ euclideanComplexInclusion
      (fullLeadingCovector T Q F row col Φ Y r (p.1, (w.2.1, p.2))))
    (fun p ↦ fullCorrectionCovector T Q F row col Φ Y r (p.1, (w.2.1, p.2)))
    (w.1, w.2.2)

/-- The literal leading principal matrix from the actual corrected family,
including its sign, complex inclusion and Frobenius norm
(`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
def fullLeadingPrincipalMatrix
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : Matrix (Fin N) (Fin n) ℂ :=
  (principalMatrix
    (principalNormal (canonicalNormalCompletion F w.1) (phaseGradient T Q w.1 w.2.2)
      (fullLeadingCovector T Q F row col Φ Y r w)) (phaseGradient T Q w.1 w.2.2)).map
        Complex.ofReal

/-- The correction's actual complex principal normal; its quantitative
bound must be deduced from the geometric reconstruction and covector bound
(`app:ch_waves:eq:exact-W-amplitude`). -/
def fullCorrectionPrincipalNormal
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : EuclideanSpace ℂ (Fin N) :=
  canonicalPrincipalNormalComplex F w.1 (scalarDifferential (fun x ↦ phase T Q x w.2.2) w.1)
    (fullCorrectionCovector T Q F row col Φ Y r w)

/-- The correction's actual reconstructed coefficient, retaining both
quadratures and all zeroth-order terms (`app:ch_waves:eq:exact-W-amplitude`). -/
def fullCorrectionReconstruction
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : EuclideanSpace ℂ (Fin N) :=
  completedVariationComplex F
    (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2)) 0 w.1

/-- The full derivative definition is the physical differential of the same
literal displacement polynomial, with no alternative amplitude
(`app:ch_waves:eq:individual-representation`). -/
theorem fullDerivativeAmplitude_apply (τ : ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) (i : Fin N) (j : Fin n) :
    fullDerivativeAmplitude T Q F row col Φ Y r τ w i j =
      waveFirstAmplitude τ⁻¹ (fun x ↦ phase T Q x w.2.2)
        (fun x ↦ fullDisplacementAmplitude T Q F row col Φ Y r τ (x, w.2))
          w.1 (EuclideanSpace.single j 1) i := rfl

end JanetCartan.RawPrimary
