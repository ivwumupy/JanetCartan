module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial.Formulas
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.ActualReconstruction

/-!
# Identification with the published full primary amplitudes

No new atom is selected here: these identities use `fullDisplacementAmplitude`,
`fullDerivativeAmplitude`, and the literal signed `fullLeadingPrincipalMatrix`.
The four named coefficients are exactly those in the original canonical
reconstruction (`app:ch_waves:eq:exact-W-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.AmplitudeGrades.Polynomial
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

/-- The literal complex leading normal in the published displacement
polynomial (`app:ch_waves:eq:exact-W-amplitude`). -/
def fullLeadingNormal (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) :
    EuclideanSpace ℂ (Fin N) :=
  canonicalPrincipalNormalComplex F w.1
    (scalarDifferential (fun x ↦ phase T Q x w.2.2) w.1)
    (euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r w))

/-- The literal leading reconstruction in that SAME polynomial
(`app:ch_waves:eq:exact-W-amplitude`). -/
def fullLeadingReconstruction (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) :
    EuclideanSpace ℂ (Fin N) :=
  completedVariationComplex F
    (fun x ↦ euclideanComplexInclusion
      (fullLeadingCovector T Q F row col Φ Y r (x, w.2))) 0 w.1

/-- The leading complex normal is precisely the inclusion of the retained
real normal from `Correction.ActualFamily`
(`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
theorem fullLeadingNormal_eq_inclusion
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) :
    fullLeadingNormal T Q F row col Φ Y r w =
      euclideanComplexInclusion (principalNormal (canonicalNormalCompletion F w.1)
        (phaseGradient T Q w.1 w.2.2) (fullLeadingCovector T Q F row col Φ Y r w)) := by
  unfold fullLeadingNormal
  rw [canonicalPrincipalNormalComplex_inclusion, scalarDifferential_eq_gradient]
  rfl

/-- The leading reconstruction embeds the retained real coefficient when
its actual covector is differentiable. Thus the real budget producer applies
without replacing the polynomial (`app:ch_waves:eq:exact-W-amplitude`). -/
theorem fullLeadingReconstruction_eq_inclusion
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hb : DifferentiableAt ℝ
      (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1) :
    fullLeadingReconstruction T Q F row col Φ Y r w =
      euclideanComplexInclusion (reconstruction F (canonicalNormalCompletion F)
        (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1) :=
  completedVariationComplex_zero_inclusion F hb

/-- The full displacement is exactly the joint three-power polynomial of
its four literal coefficients (`app:ch_waves:eq:exact-W-amplitude`). -/
theorem fullDisplacementAmplitude_eq_polynomial (τ : ℝ) :
    fullDisplacementAmplitude T Q F row col Φ Y r τ =
      WKB.reconstructionAmplitude τ⁻¹
        (fullLeadingNormal T Q F row col Φ Y r)
        (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
        (fullLeadingReconstruction T Q F row col Φ Y r)
        (fullCorrectionReconstruction T Q F row col Φ Y r) := rfl

/-- The leading term has exactly the published negative sign and complex
inclusion, as a Frobenius matrix (`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
theorem fullLeadingPrincipalMatrix_eq_tensor
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) :
    fullLeadingPrincipalMatrix T Q F row col Φ Y r w =
      -(normalTensor n N (phaseGradient T Q w.1 w.2.2)
        (fullLeadingNormal T Q F row col Φ Y r w)) := by
  rw [fullLeadingNormal_eq_inclusion]
  ext i j
  simp only [fullLeadingPrincipalMatrix, principalMatrix, Matrix.map_apply,
    Matrix.neg_apply, normalTensor_apply, euclideanComplexInclusion_apply,
    Complex.ofReal_neg, Complex.ofReal_mul]
  ring

/-- The SAME full derivative amplitude is the exact joint matrix
polynomial, with smoothness only of its four geometric coefficients and its
actual phase. The latter comes from `contDiffOn_fullPhase`
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem fullDerivativeAmplitude_eq_polynomial {τ : ℝ} (hτ : τ ≠ 0)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hS : DifferentiableAt ℝ (fun y ↦ phase T Q y.1 y.2.2) w)
    (hν₀ : DifferentiableAt ℝ (fullLeadingNormal T Q F row col Φ Y r) w)
    (hν₁ : DifferentiableAt ℝ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) w)
    (hV₀ : DifferentiableAt ℝ (fullLeadingReconstruction T Q F row col Φ Y r) w)
    (hV₁ : DifferentiableAt ℝ (fullCorrectionReconstruction T Q F row col Φ Y r) w) :
    fullDerivativeAmplitude T Q F row col Φ Y r τ w =
      derivativePolynomial τ (fun y ↦ phaseGradient T Q y.1 y.2.2)
        (fullLeadingNormal T Q F row col Φ Y r)
        (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
        (fullLeadingReconstruction T Q F row col Φ Y r)
        (fullCorrectionReconstruction T Q F row col Φ Y r) w := by
  ext i j
  rw [fullDerivativeAmplitude_apply, fullDisplacementAmplitude_eq_polynomial]
  simpa only [scalarDifferential_eq_gradient, phaseGradient] using
    (derivativePolynomial_apply hτ hS hν₀ hν₁ hV₀ hV₁ i j).symm

/-- Exact error against the literal leading principal matrix for the SAME
published full amplitude (`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem fullDerivativeAmplitude_sub_principal_eq {τ : ℝ} (hτ : τ ≠ 0)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hS : DifferentiableAt ℝ (fun y ↦ phase T Q y.1 y.2.2) w)
    (hν₀ : DifferentiableAt ℝ (fullLeadingNormal T Q F row col Φ Y r) w)
    (hν₁ : DifferentiableAt ℝ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) w)
    (hV₀ : DifferentiableAt ℝ (fullLeadingReconstruction T Q F row col Φ Y r) w)
    (hV₁ : DifferentiableAt ℝ (fullCorrectionReconstruction T Q F row col Φ Y r) w) :
    fullDerivativeAmplitude T Q F row col Φ Y r τ w -
      fullLeadingPrincipalMatrix T Q F row col Φ Y r w =
        derivativeError τ (fun y ↦ phaseGradient T Q y.1 y.2.2)
          (fullLeadingNormal T Q F row col Φ Y r)
          (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
          (fullLeadingReconstruction T Q F row col Φ Y r)
          (fullCorrectionReconstruction T Q F row col Φ Y r) w := by
  rw [fullDerivativeAmplitude_eq_polynomial T Q F row col Φ Y r hτ hS hν₀ hν₁ hV₀ hV₁,
    fullLeadingPrincipalMatrix_eq_tensor, derivativePolynomial]
  abel

end JanetCartan.RawPrimary.AmplitudeGrades.Polynomial
