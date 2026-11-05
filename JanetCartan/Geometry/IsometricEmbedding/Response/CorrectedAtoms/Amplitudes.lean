module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.RetainedFamily
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Definitions

/-!
# The corrected amplitude on the original phase

For `app:ch_response:cor:current-atoms`, the corrected derivative amplitude is
the existing raw derivative amplitude minus the demodulated PHYSICAL derivative
of its response. The theorem below identifies this formula with the derivative
of the literal corrected field. In particular no phase or leading tensor is
reselected. The bounds consumed by `CorrectedAtoms.ResponseDensity` must be
proved for these same amplitudes by the raw and response producers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.CorrectedAtoms
open RawPrimary LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

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

/-- The demodulated PHYSICAL derivative of the response, including its carrier
derivative term (`app:ch_response:eq:current-atomic-amplitudes`). -/
def fullPrimaryResponseDerivativeAmplitude (τ : ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : Matrix (Fin N) (Fin n) ℂ :=
  Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ)) •
    (fun i j ↦ partialDeriv (fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2) w.1 j i)

/-- The derivative amplitude after the one fixed solve, using the same leading
amplitude and original phase (`app:ch_response:cor:current-atoms`). -/
def fullCorrectedDerivativeAmplitude (τ : ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : Matrix (Fin N) (Fin n) ℂ :=
  fullDerivativeAmplitude T Q F row col Φ Y r τ w -
    fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ w

/-- The corrected amplitude is exactly the demodulated derivative of the
literal corrected atom. All raw regularity is discharged from its retained
leading outputs. The remaining response differentiability is supplied by
`contDiff_fullPrimaryResponse_ambientExtension`
(`app:ch_response:eq:current-atomic-amplitudes`). -/
theorem fullCorrectedDerivativeAmplitude_eq_demodulated
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    {τ : ℝ} (hτ : τ ≠ 0)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω)
    (hB : DifferentiableAt ℝ (fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2) w.1) :
    fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w =
      Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ)) •
        (fun i j ↦ partialDeriv
          (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r w.2) w.1 j i) := by
  let O : Set (Euclidean n) := {x | (x, w.2) ∈ Ω}
  have ho : IsOpen O := hΩ.preimage (continuous_id.prodMk continuous_const)
  have hs {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → E}
      (hf : ContDiffOn ℝ ∞ f Ω) : ContDiffOn ℝ ∞ (fun x ↦ f (x, w.2)) O :=
    hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx ↦ hx)
  have hS := hs (contDiffOn_fullPhase T Q hphase)
  have hb₀ := hs ((euclideanComplexInclusion (ι := Fin n)).contDiff.comp_contDiffOn
    (contDiffOn_fullLeadingCovector T Q F row col Φ Y r hspace hphase hα))
  have hb₁ := hs (contDiffOn_fullCorrectionCovector_of_leading_outputs
    T Q F row col Φ Y r hΩ hspace hphase hF hi hα hnonzero)
  have hA := hs (contDiffOn_fullDisplacementAmplitude_of_leading_outputs
    T Q F row col Φ Y r hτ hΩ hspace hphase hF hi hrank hα hnonzero)
  have hW := ((hs (contDiffOn_fullPrimaryAtom_of_leading_outputs
    T Q F row col Φ Y r τ hΩ hspace hphase hF hi hrank hα hnonzero)).contDiffAt
      (ho.mem_nhds hw)).differentiableAt (by simp)
  have hraw := canonicalAtomDerivative_eq F hτ
    (S := fun p ↦ phase T Q p.1 p.2)
    (b₀ := fun p ↦ euclideanComplexInclusion
      (fullLeadingCovector T Q F row col Φ Y r (p.1, (w.2.1, p.2))))
    (b₁ := fun p ↦ fullCorrectionCovector T Q F row col Φ Y r (p.1, (w.2.1, p.2)))
    ho hw w.2.2 (hS.differentiableOn (by simp)) (hb₀.differentiableOn (by simp))
    (hb₁.differentiableOn (by simp)) ((hA.contDiffAt (ho.mem_nhds hw)).differentiableAt
      (by simp))
  change (fun i j ↦ partialDeriv
      (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2)) w.1 j i) =
    Complex.exp (Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ)) •
      fullDerivativeAmplitude T Q F row col Φ Y r τ w at hraw
  have he : Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ)) *
      Complex.exp (Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ)) = 1 := by
    rw [← Complex.exp_add]
    simp only [neg_mul, neg_add_cancel, Complex.exp_zero]
  have hd : fderiv ℝ (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r w.2) w.1 =
      fderiv ℝ (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2)) w.1 -
        fderiv ℝ (fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2) w.1 :=
    fderiv_sub hW hB
  ext i j
  have hij := congrArg (fun a : Matrix (Fin N) (Fin n) ℂ ↦ a i j) hraw
  change fullDerivativeAmplitude T Q F row col Φ Y r τ w i j -
      Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ)) *
        (fderiv ℝ (fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2) w.1
          (EuclideanSpace.single j 1)) i =
    Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ)) *
      (fderiv ℝ (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r w.2) w.1
        (EuclideanSpace.single j 1)) i
  rw [hd]
  simp only [sub_apply, PiLp.sub_apply]
  simp only [partialDeriv, Matrix.smul_apply, smul_eq_mul] at hij
  rw [hij, mul_sub, ← mul_assoc, he, one_mul]

end JanetCartan.CorrectedAtoms
