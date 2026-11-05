module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Phase
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.SourceIntegration

/-!
# Source-transform algebra for derivative transfer

For `app:ch_regular_base:eq:graph-derivative-transfer`, source integration by
parts identifies the output-derivative amplitude with the transferred amplitude
and a derivative of the datum. All amplitudes retain both physical positions.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff RealInnerProductSpace
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: source integration is
additive in continuous amplitudes on a compactly supported continuous datum. -/
theorem sourceAmplitudeTransform_add_of_compactSupport
    (c e : V → V → V → ℂ) (u : V → ℂ) (x ξ : V)
    (hu : Continuous u) (hus : HasCompactSupport u)
    (hc : Continuous (fun y ↦ c x y ξ)) (he : Continuous (fun y ↦ e x y ξ)) :
    sourceAmplitudeTransform (fun x y ξ ↦ c x y ξ + e x y ξ) u x ξ =
      sourceAmplitudeTransform c u x ξ + sourceAmplitudeTransform e u x ξ := by
  have hi₁ : Integrable (fun y ↦ u y * c x y ξ) :=
    (hu.mul hc).integrable_of_hasCompactSupport hus.mul_right
  have hi₂ : Integrable (fun y ↦ u y * e x y ξ) :=
    (hu.mul he).integrable_of_hasCompactSupport hus.mul_right
  simp only [sourceAmplitudeTransform, Real.fourier_eq, smul_eq_mul, mul_add, smul_add]
  exact integral_add ((Real.fourierIntegral_convergent_iff ξ).mpr hi₁)
    ((Real.fourierIntegral_convergent_iff ξ).mpr hi₂)

/-- `app:ch_regular_base:eq:fio-input`: a complex frequency multiplier
commutes with the source transform of the complete amplitude. -/
theorem sourceAmplitudeTransform_frequency_mul
    (c : V → V → V → ℂ) (u : V → ℂ) (a : V → ℂ) (x ξ : V) :
    sourceAmplitudeTransform (fun x y ξ ↦ a ξ * c x y ξ) u x ξ =
      a ξ * sourceAmplitudeTransform c u x ξ := by
  simp only [sourceAmplitudeTransform, Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: after source
integration by parts, the output-derivative amplitude is the transferred
amplitude plus the original amplitude acting on the coordinate derivative of
the datum. This identity is pointwise in the output position and frequency. -/
theorem sourceAmplitudeTransform_outputDerivativeAmplitude
    {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (i : Fin d)
    (u : EuclideanSpace ℝ (Fin d) → ℂ) (hu : ContDiff ℝ ∞ u)
    (hus : HasCompactSupport u) (x ξ : EuclideanSpace ℝ (Fin d)) :
    sourceAmplitudeTransform
        (fun x y ξ ↦ outputDerivativeAmplitude b i ξ (pairedPosition x y)) u x ξ =
      sourceAmplitudeTransform
        (fun x y ξ ↦ transferAmplitude b i ξ (pairedPosition x y)) u x ξ +
      sourceAmplitudeTransform (fun x y ξ ↦ b ξ (pairedPosition x y))
        (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x ξ := by
  have hc (ξ : EuclideanSpace ℝ (Fin d)) :
      ContDiff ℝ ∞ (fun y ↦ b ξ (pairedPosition x y)) :=
    (hb ξ).comp (contDiff_pairedPosition.comp (contDiff_const.prodMk contDiff_id))
  have hp (j : Fin (2 * d)) : Continuous (fun y ↦
      euclideanCoordinateDerivList [j] (b ξ) (pairedPosition x y)) :=
    (contDiff_euclideanCoordinateDerivList (hb ξ) [j]).continuous.comp
      (continuous_pairedPosition.comp (continuous_const.prodMk continuous_id))
  have h := sourceAmplitudeTransform_sourceDerivative_add_inputDerivative
    (fun x y ξ ↦ b ξ (pairedPosition x y)) u x ξ (EuclideanSpace.single i 1)
    hu hus (hc ξ)
  simp_rw [fderiv_pairedPosition_right_apply _ ((hb _).differentiable (by simp))] at h
  rw [real_inner_comm] at h
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] at h
  unfold outputDerivativeAmplitude transferAmplitude
  rw [sourceAmplitudeTransform_add_of_compactSupport _ _ u x ξ hu.continuous hus
    (hp _) (continuous_const.mul (hc ξ).continuous)]
  rw [sourceAmplitudeTransform_add_of_compactSupport _ _ u x ξ hu.continuous hus
    (hp _) (hp _)]
  rw [sourceAmplitudeTransform_frequency_mul]
  rw [← h, add_assoc]

end JanetCartan.Pseudodifferential
