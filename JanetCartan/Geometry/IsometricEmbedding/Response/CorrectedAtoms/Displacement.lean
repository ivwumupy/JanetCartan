module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.JointRegularity

/-!
# Literal corrected displacement on the original phase

For `app:ch_response:cor:current-atoms`, identify the corrected field with its
amplitude on the same phase used by the raw and sampling consumers. Both
response amplitudes use the one supplied operator. Joint response regularity
is the precise input owned by `Response.SmoothParameters`; it is not inferred
from separate physical smoothness or from a new response choice.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CorrectedAtoms
open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- The literal demodulated response field in
`app:ch_response:eq:current-atomic-amplitudes`, with the original phase. -/
def fullPrimaryResponseDisplacementAmplitude (τ : ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : EuclideanSpace ℂ (Fin N) :=
  Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ)) •
    fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1

/-- The corrected displacement amplitude subtracts the SAME response field
from the literal raw polynomial (`app:ch_response:cor:current-atoms`). -/
def fullCorrectedDisplacementAmplitude (τ : ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : EuclideanSpace ℂ (Fin N) :=
  fullDisplacementAmplitude T Q F row col Φ Y r τ w -
    fullPrimaryResponseDisplacementAmplitude T Q F row col Φ Y χ B r τ w

variable {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)

include hΩ hspace hphase hF hi hα hnonzero

/-- The corrected atom has exactly the original oscillatory phase. No
regularity of the response is needed for this algebraic identity, and no
frequency-dependent representative is selected
(`app:ch_response:cor:current-atoms`, `app:ch_waves:eq:individual-representation`). -/
theorem fullCorrectedPrimaryAtom_eq_modulated {τ : ℝ} (hτ : τ ≠ 0)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω) :
    fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r w.2 w.1 =
      Complex.exp (Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ)) •
        fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ w := by
  change fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (w.1, w.2.2) -
    fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1 = _
  rw [fullPrimaryAtom_eq_of_leading_outputs T Q F row col Φ Y r hτ
    hΩ hspace hphase hF hi hα hnonzero hw]
  unfold fullCorrectedDisplacementAmplitude fullPrimaryResponseDisplacementAmplitude
  rw [smul_sub, smul_smul, ← Complex.exp_add]
  simp only [neg_mul, add_neg_cancel, Complex.exp_zero, one_smul]

/-- Demodulation of the literal corrected field recovers its SAME displacement
amplitude (`app:ch_response:eq:current-atomic-amplitudes`). -/
theorem fullCorrectedDisplacementAmplitude_eq_demodulated {τ : ℝ} (hτ : τ ≠ 0)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω) :
    fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ w =
      Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ)) •
        fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r w.2 w.1 := by
  rw [fullCorrectedPrimaryAtom_eq_modulated T Q F row col Φ Y χ B r
    hΩ hspace hphase hF hi hα hnonzero hτ hw, smul_smul, ← Complex.exp_add]
  simp only [neg_mul, neg_add_cancel, Complex.exp_zero, one_smul]

omit hΩ hspace hF hi hα hnonzero in
/-- Joint regularity of the fixed response gives joint regularity of its
literal displacement envelope (`app:ch_response:eq:current-atomic-amplitudes`).
The producer is `both-fixed-response-parameters`, on this same source and `B`. -/
theorem contDiffOn_fullPrimaryResponseDisplacementAmplitude (τ : ℝ)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω) :
    ContDiffOn ℝ ∞ (fullPrimaryResponseDisplacementAmplitude T Q F row col Φ Y χ B r τ) Ω :=
  ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((contDiffOn_fullPhase T Q hphase).div_const τ))).cexp).smul hresponse

include hrank

/-- The physical derivative of the literal corrected field has exactly the
original phase and corrected derivative amplitude. This is the pointwise
representation used by `CanonicalAtomRealization` before integration
(`app:ch_waves:eq:individual-representation`, `app:ch_response:cor:current-atoms`). -/
theorem fullCorrectedPrimaryAtom_derivative_eq_modulated {τ : ℝ} (hτ : τ ≠ 0)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω)
    (hB : DifferentiableAt ℝ (fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2) w.1) :
    (fun i j ↦ partialDeriv
      (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r w.2) w.1 j i) =
      Complex.exp (Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ)) •
        fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w := by
  rw [fullCorrectedDerivativeAmplitude_eq_demodulated T Q F row col Φ Y χ B r
    hΩ hspace hphase hF hi hrank hα hnonzero hτ hw hB,
    smul_smul, ← Complex.exp_add]
  simp only [neg_mul, add_neg_cancel, Complex.exp_zero, one_smul]

/-- Joint smoothness of the actual corrected field follows by subtracting the
same fixed response from the retained raw field. This supplies the regularity
needed for compact carrier integration (`app:ch_response:cor:current-atoms`). -/
theorem contDiffOn_fullCorrectedPrimaryAtom_joint (τ : ℝ)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω) :
    ContDiffOn ℝ ∞
      (fun w ↦ fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r w.2 w.1) Ω :=
  (contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
    hΩ hspace hphase hF hi hrank hα hnonzero).sub hresponse

/-- Joint smoothness of the literal corrected displacement amplitude from the
retained raw construction and the same response output. The source cutoff and
phase are unchanged (`app:ch_response:cor:current-atoms`). -/
theorem contDiffOn_fullCorrectedDisplacementAmplitude {τ : ℝ} (hτ : τ ≠ 0)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω) :
    ContDiffOn ℝ ∞ (fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ) Ω :=
  (contDiffOn_fullDisplacementAmplitude_of_leading_outputs T Q F row col Φ Y r hτ
    hΩ hspace hphase hF hi hrank hα hnonzero).sub
    (contDiffOn_fullPrimaryResponseDisplacementAmplitude T Q F row col Φ Y χ B r hphase τ hresponse)

/-- Joint smoothness of the literal corrected physical derivative amplitude,
used by the canonical raw and sampling consumers. The response regularity
input remains the one for the same fixed operator
(`app:ch_response:eq:current-atomic-amplitudes`). -/
theorem contDiffOn_fullCorrectedDerivativeAmplitude {τ : ℝ} (hτ : τ ≠ 0)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω) :
    ContDiffOn ℝ ∞ (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ) Ω :=
  (contDiffOn_retainedDerivativeAmplitude T Q F row col Φ Y r
    hΩ hspace hphase hF hi hrank hα hnonzero hτ).sub
    (contDiffOn_fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y r
      hΩ hphase χ B τ hresponse)

end JanetCartan.CorrectedAtoms
