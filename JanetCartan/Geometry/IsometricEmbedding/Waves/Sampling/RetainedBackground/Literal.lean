module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Reconstruction.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.Hermitian

/-!
# The original zero-input background tensor

The background in `app:ch_waves:eq:background-quadrature` is the real Hermitian
tensor of the differential of the original `η = 0` atom. Its spatial cutoff
multiplies the tensor, rather than being differentiated as part of the wave.
The phase cancels exactly, leaving the SAME full derivative amplitude.
These identities are consumed by the retained background estimates; they do
not assume an estimate for the resulting tensor.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.RetainedBackground
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open AmbientResponse ResponseTransfer

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- The localized real Hermitian tensor of the original background field,
with the original carrier covector and no Fourier mask or radial band
(`app:ch_waves:eq:background-quadrature`). -/
def localizedBackground (χ : Euclidean n → ℝ) (τ : ℝ)
    (z : Euclidean 3) (x : Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  χ x • hermitianTensor (RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N
    (fderiv ℝ (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z
      (y, T.reference.spatialPatch z)) x))

/-- The smooth inverse-frequency polynomial for the SAME background before
restriction to the carrier graph. It retains every correction coefficient
(`app:ch_waves:eq:background-quadrature`). -/
def backgroundPolynomial (τ : ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) :
    Matrix (Fin n) (Fin n) ℝ :=
  hermitianTensor (derivativePolynomial τ (fun y ↦ phaseGradient T Q y.1 y.2.2)
    (fullLeadingNormal T Q F row col Φ Y r)
    (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
    (fullLeadingReconstruction T Q F row col Φ Y r)
    (fullCorrectionReconstruction T Q F row col Φ Y r) w)

/-- Exact demodulation of the original atom's differential. All regularity
inputs are outputs of the retained leading construction; smoothness of the
actual displacement is derived from them
(`app:ch_waves:eq:individual-representation`). -/
theorem background_differential_eq
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    {τ : ℝ} (hτ : τ ≠ 0) {z : Euclidean 3} {x : Euclidean n}
    (hw : (x, (z, T.reference.spatialPatch z)) ∈ Ω) :
    RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N
        (fderiv ℝ (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z
          (y, T.reference.spatialPatch z)) x) =
      Complex.exp (Complex.I * (T.carrier Q x z / τ : ℝ)) •
        fullDerivativeAmplitude T Q F row col Φ Y r τ (x, (z, T.reference.spatialPatch z)) := by
  let ξ := T.reference.spatialPatch z
  have hs : ContDiffAt ℝ ∞ (fun y ↦ phase T Q y ξ) x :=
    ((contDiffOn_fullPhase T Q hphase).contDiffAt (hΩ.mem_nhds hw)).comp
      (f := fun y ↦ (y, (z, ξ))) x
      (contDiffAt_id.prodMk contDiffAt_const)
  have ha : ContDiffAt ℝ ∞
      (fun y ↦ fullDisplacementAmplitude T Q F row col Φ Y r τ (y, (z, ξ))) x :=
    ((contDiffOn_fullDisplacementAmplitude_of_leading_outputs T Q F row col Φ Y r hτ
      hΩ hspace hphase hF hi hrank hα hnonzero).contDiffAt (hΩ.mem_nhds hw)).comp
        (f := fun y ↦ (y, (z, ξ))) x
        (contDiffAt_id.prodMk contDiffAt_const)
  have he : (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z (y, ξ)) =ᶠ[𝓝 x]
      modulatedWave τ⁻¹ (fun y ↦ phase T Q y ξ)
        (fun y ↦ fullDisplacementAmplitude T Q F row col Φ Y r τ (y, (z, ξ))) := by
    have hm : ∀ᶠ y in 𝓝 x, (y, (z, ξ)) ∈ Ω :=
      (continuous_id.prodMk continuous_const).continuousAt (hΩ.mem_nhds hw)
    filter_upwards [hm] with y hy
    rw [fullPrimaryAtom_eq_of_leading_outputs T Q F row col Φ Y r hτ
      hΩ hspace hphase hF hi hα hnonzero hy]
    simp only [modulatedWave, waveCarrier_inv_eq_exp_div, Complex.ofReal_div, mul_div_assoc]
  ext i j
  change fderiv ℝ (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z (y, ξ)) x
      (EuclideanSpace.single j 1) i = _
  rw [he.fderiv_eq, fderiv_modulatedWave (hs.differentiableAt (by simp))
    (ha.differentiableAt (by simp))]
  simp only [waveCarrier_inv_eq_exp_div, Complex.ofReal_div, mul_div_assoc,
    PiLp.smul_apply, smul_eq_mul, Matrix.smul_apply, fullDerivativeAmplitude_apply]
  rfl

/-- The unit complex phase cancels in the actual localized Hermitian tensor,
as required before Taylor expansion in `app:ch_waves:eq:background-quadrature`.
This uses the original zero-input atom, not a prepared scalar specialization. -/
theorem localizedBackground_eq_amplitude
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (χ : Euclidean n → ℝ) {τ : ℝ} (hτ : τ ≠ 0) {z : Euclidean 3} {x : Euclidean n}
    (hw : (x, (z, T.reference.spatialPatch z)) ∈ Ω) :
    localizedBackground T Q F row col Φ Y r χ τ z x =
      χ x • hermitianTensor
        (fullDerivativeAmplitude T Q F row col Φ Y r τ (x, (z, T.reference.spatialPatch z))) := by
  rw [localizedBackground, background_differential_eq T Q F row col Φ Y r
    hΩ hspace hphase hF hi hrank hα hnonzero hτ hw, hermitianTensor_smul]
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
  simp

/-- At nonzero frequency, the background polynomial is the Hermitian tensor
of the SAME full derivative amplitude. The coefficient smoothness is supplied
by the leading and correction reconstruction producers
(`app:ch_waves:eq:background-quadrature`). -/
theorem backgroundPolynomial_eq_amplitude {τ : ℝ} (hτ : τ ≠ 0)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hS : DifferentiableAt ℝ (fun y ↦ phase T Q y.1 y.2.2) w)
    (hν₀ : DifferentiableAt ℝ (fullLeadingNormal T Q F row col Φ Y r) w)
    (hν₁ : DifferentiableAt ℝ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) w)
    (hV₀ : DifferentiableAt ℝ (fullLeadingReconstruction T Q F row col Φ Y r) w)
    (hV₁ : DifferentiableAt ℝ (fullCorrectionReconstruction T Q F row col Φ Y r) w) :
    backgroundPolynomial T Q F row col Φ Y r τ w =
      hermitianTensor (fullDerivativeAmplitude T Q F row col Φ Y r τ w) := by
  rw [fullDerivativeAmplitude_eq_polynomial T Q F row col Φ Y r hτ hS hν₀ hν₁ hV₀ hV₁]
  rfl

/-- Identify the actual localized background with its smooth polynomial,
discharging all four coefficient-regularity inputs from the original retained
leading outputs. This is the literal matching used when applying the joint
budgets, not an assumed amplitude identity
(`app:ch_waves:eq:background-quadrature`). -/
theorem localizedBackground_eq_polynomial_of_leading_outputs
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (χ : Euclidean n → ℝ) {τ : ℝ} (hτ : τ ≠ 0) {z : Euclidean 3} {x : Euclidean n}
    (hw : (x, (z, T.reference.spatialPatch z)) ∈ Ω) :
    localizedBackground T Q F row col Φ Y r χ τ z x =
      χ x • backgroundPolynomial T Q F row col Φ Y r τ
        (x, (z, T.reference.spatialPatch z)) := by
  have hb₀ : ContDiffOn ℝ ∞ (fun w ↦ euclideanComplexInclusion
      (fullLeadingCovector T Q F row col Φ Y r w)) Ω :=
    (euclideanComplexInclusion (ι := Fin n)).contDiff.comp_contDiffOn
      (contDiffOn_fullLeadingCovector T Q F row col Φ Y r hspace hphase hα)
  have hb₁ := contDiffOn_fullCorrectionCovector_of_leading_outputs
    T Q F row col Φ Y r hΩ hspace hphase hF hi hα hnonzero
  have hξ : ContDiffOn ℝ ∞ (fun w ↦ phaseGradient T Q w.1 w.2.2) Ω :=
    (phaseGradient_smooth T Q).comp
      (contDiffOn_fst.prodMk contDiffOn_snd.snd) hphase
  have he₀ : fullLeadingNormal T Q F row col Φ Y r = fun w ↦
      canonicalPrincipalNormalComplex F w.1 (phaseGradient T Q w.1 w.2.2)
        (euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r w)) := by
    funext w
    simp only [fullLeadingNormal, scalarDifferential_eq_gradient, phaseGradient]
  have he₁ : fullCorrectionPrincipalNormal T Q F row col Φ Y r = fun w ↦
      canonicalPrincipalNormalComplex F w.1 (phaseGradient T Q w.1 w.2.2)
        (fullCorrectionCovector T Q F row col Φ Y r w) := by
    funext w
    simp only [fullCorrectionPrincipalNormal, scalarDifferential_eq_gradient, phaseGradient]
  have hν₀ : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω := by
    rw [he₀]
    exact contDiffOn_joint_canonicalPrincipalNormalComplex_of_isOpen
      (F := F) hΩ hspace hF hb₀ hξ hi hrank
  have hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω := by
    rw [he₁]
    exact contDiffOn_joint_canonicalPrincipalNormalComplex_of_isOpen
      (F := F) hΩ hspace hF hb₁ hξ hi hrank
  have heV₀ : fullLeadingReconstruction T Q F row col Φ Y r = fun w ↦
      completedVariationComplex F (fun y ↦ euclideanComplexInclusion
        (fullLeadingCovector T Q F row col Φ Y r (y, w.2))) 0 w.1 := rfl
  have heV₁ : fullCorrectionReconstruction T Q F row col Φ Y r = fun w ↦
      completedVariationComplex F (fun y ↦
        fullCorrectionCovector T Q F row col Φ Y r (y, w.2)) 0 w.1 := rfl
  have hV₀ : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω := by
    rw [heV₀]
    exact contDiffOn_joint_completedVariationComplex_zero_of_isOpen
      (F := F) (b := fun w ↦ euclideanComplexInclusion
        (fullLeadingCovector T Q F row col Φ Y r w)) hΩ hspace hF hb₀ hi hrank
  have hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω := by
    rw [heV₁]
    exact contDiffOn_joint_completedVariationComplex_zero_of_isOpen
      (F := F) (b := fullCorrectionCovector T Q F row col Φ Y r)
      hΩ hspace hF hb₁ hi hrank
  rw [localizedBackground_eq_amplitude T Q F row col Φ Y r
    hΩ hspace hphase hF hi hrank hα hnonzero χ hτ hw,
    backgroundPolynomial_eq_amplitude T Q F row col Φ Y r hτ
      (((contDiffOn_fullPhase T Q hphase).contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp))
      ((hν₀.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp))
      ((hν₁.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp))
      ((hV₀.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp))
      ((hV₁.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp))]

/-- The zero-frequency endpoint is precisely the original transported
rank-one tensor. This is the comparison target adjacent to
`app:ch_waves:eq:background-quadrature`; it retains the original scalar. -/
theorem backgroundPolynomial_zero
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) :
    backgroundPolynomial T Q F row col Φ Y r 0 w =
      fun i j ↦ ‖principalNormal (canonicalNormalCompletion F w.1)
        (phaseGradient T Q w.1 w.2.2) (fullLeadingCovector T Q F row col Φ Y r w)‖ ^ 2 *
          phaseGradient T Q w.1 w.2.2 i * phaseGradient T Q w.1 w.2.2 j := by
  have he : derivativePolynomial 0 (fun y ↦ phaseGradient T Q y.1 y.2.2)
      (fullLeadingNormal T Q F row col Φ Y r)
      (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
      (fullLeadingReconstruction T Q F row col Φ Y r)
      (fullCorrectionReconstruction T Q F row col Φ Y r) w =
        fullLeadingPrincipalMatrix T Q F row col Φ Y r w := by
    rw [fullLeadingPrincipalMatrix_eq_tensor]
    simp [derivativePolynomial, derivativeError]
  rw [backgroundPolynomial, he]
  exact principalMatrix_hermitianTensor _ _

end JanetCartan.Sampling.RetainedBackground
