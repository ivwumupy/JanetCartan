module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Derivatives
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Euclidean profiles for the fixed periodic cutoff

The Euclidean part of the kernel estimate in `main:lem:smoothing` and
`main:eq:smoothing-low`. The frequency profile includes `2π`, so its samples
at `k / R` agree with the already fixed `periodicCutoffSymbol R k`.
The inverse Fourier transform is Schwartz, and its dilates have derivative
L¹ masses exactly proportional to `R ^ j`. The passage to the torus still
requires a periodization theorem.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff

namespace JanetCartan

/-- `main:lem:smoothing`: the same fixed cutoff in Mathlib's `2π` Fourier
normalization, bundled as a complex Schwartz function. -/
def cutoffFrequencyProfile (n : ℕ) : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  ((hasCompactSupport_fourierCutoff.comp_homeomorph
    (Homeomorph.smulOfNeZero (2 * Real.pi) (by positivity))).comp_left
      (show (0 : ℝ) = (0 : ℂ) from Complex.ofReal_zero)).toSchwartzMap
    (by
      change ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) ↦
        (fourierCutoff ((2 * Real.pi) • x) : ℂ))
      exact Complex.ofRealCLM.contDiff.comp
        (contDiff_fourierCutoff.comp (contDiff_id.const_smul (2 * Real.pi))))

/-- `main:lem:smoothing`: the frequency profile retains the exact fixed symbol. -/
@[simp] theorem cutoffFrequencyProfile_apply (n : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) :
    cutoffFrequencyProfile n ξ = (fourierCutoff ((2 * Real.pi) • ξ) : ℂ) := rfl

/-- `main:lem:smoothing`: sampling the profile gives the existing cutoff,
including its `2π / R` normalization. -/
theorem cutoffFrequencyProfile_scaled_integer (n : ℕ) (R : ℝ) (k : Fin n → ℤ) :
    cutoffFrequencyProfile n
      (R⁻¹ • (WithLp.toLp 2 (fun i ↦ (k i : ℝ)) : EuclideanSpace ℝ (Fin n))) =
      (periodicCutoffSymbol R k : ℂ) := by
  simp [periodicCutoffSymbol, smul_smul, div_eq_mul_inv]

/-- `main:lem:smoothing`: the fixed Euclidean convolution profile. -/
def cutoffSpatialProfile (n : ℕ) : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  𝓕⁻ (cutoffFrequencyProfile n)

/-- `main:lem:smoothing`: Fourier inversion identifies the spatial profile's
symbol, without any periodization assumption. -/
@[simp] theorem fourier_cutoffSpatialProfile (n : ℕ) :
    𝓕 (cutoffSpatialProfile n) = cutoffFrequencyProfile n :=
  FourierTransform.fourier_fourierInv_eq _

/-- `main:lem:smoothing`: Euclidean dilation with the dimensional Jacobian. -/
def cutoffEuclideanKernel (n : ℕ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  R ^ n • cutoffSpatialProfile n (R • x)

/-- `main:lem:smoothing`: the dilated kernel remains a Schwartz function
at every nonzero scale. -/
def cutoffEuclideanKernelSchwartz (n : ℕ) (R : ℝ) (hR : R ≠ 0) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  R ^ n • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (Units.mk0 R hR • ContinuousLinearEquiv.refl ℝ _) (cutoffSpatialProfile n)

/-- `main:lem:smoothing`: bundling the scaled profile changes no values. -/
@[simp] theorem cutoffEuclideanKernelSchwartz_apply (n : ℕ) (R : ℝ) (hR : R ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) :
    cutoffEuclideanKernelSchwartz n R hR x = cutoffEuclideanKernel n R x := rfl

/-- `main:lem:smoothing`: smoothness of every dilated Euclidean kernel. -/
theorem contDiff_cutoffEuclideanKernel (n : ℕ) (R : ℝ) :
    ContDiff ℝ ∞ (cutoffEuclideanKernel n R) :=
  ((cutoffSpatialProfile n).smooth ⊤ |>.comp
    (contDiff_id.const_smul R)).const_smul _

/-- `main:eq:smoothing-low`: the exact derivative scaling law. -/
theorem iteratedFDeriv_cutoffEuclideanKernel (n j : ℕ) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ j (cutoffEuclideanKernel n R) x =
      R ^ (n + j) • iteratedFDeriv ℝ j (cutoffSpatialProfile n) (R • x) := by
  unfold cutoffEuclideanKernel
  rw [iteratedFDeriv_const_smul_apply',
    iteratedFDeriv_comp_const_smul R ((cutoffSpatialProfile n).smooth j),
    smul_smul, ← pow_add]
  exact (((cutoffSpatialProfile n).smooth j).comp
    (contDiff_id.const_smul R)).contDiffAt

/-- `main:eq:smoothing-low`: each fixed profile derivative has finite L¹ mass. -/
theorem integrable_norm_iteratedFDeriv_cutoffSpatialProfile (n j : ℕ) :
    Integrable (fun x ↦ ‖iteratedFDeriv ℝ j (cutoffSpatialProfile n) x‖) := by
  simpa using (cutoffSpatialProfile n).integrable_pow_mul_iteratedFDeriv volume 0 j

/-- `main:eq:smoothing-low`: each positive-scale derivative is integrable. -/
theorem integrable_norm_iteratedFDeriv_cutoffEuclideanKernel (n j : ℕ)
    {R : ℝ} (hR : 0 < R) :
    Integrable (fun x ↦ ‖iteratedFDeriv ℝ j (cutoffEuclideanKernel n R) x‖) := by
  simp_rw [iteratedFDeriv_cutoffEuclideanKernel, norm_smul]
  exact ((integrable_norm_iteratedFDeriv_cutoffSpatialProfile n j).comp_smul
    hR.ne').const_mul _

/-- `main:eq:smoothing-low`: the nonnegative Euclidean constant independent of
scale. Periodization is needed to bound the periodic kernel by this constant. -/
def cutoffEuclideanDerivMass (n j : ℕ) : ℝ :=
  ∫ x, ‖iteratedFDeriv ℝ j (cutoffSpatialProfile n) x‖

/-- `main:eq:smoothing-low`: positivity of the fixed Euclidean mass constant. -/
theorem cutoffEuclideanDerivMass_nonneg (n j : ℕ) : 0 ≤ cutoffEuclideanDerivMass n j :=
  integral_nonneg (fun _ ↦ norm_nonneg _)

/-- `main:eq:smoothing-low`: the exact Euclidean L¹ scaling estimate at every
order, including dimension zero and derivative order zero. -/
theorem integral_norm_iteratedFDeriv_cutoffEuclideanKernel (n j : ℕ)
    {R : ℝ} (hR : 0 < R) :
    (∫ x, ‖iteratedFDeriv ℝ j (cutoffEuclideanKernel n R) x‖) =
      cutoffEuclideanDerivMass n j * R ^ j := by
  simp_rw [iteratedFDeriv_cutoffEuclideanKernel, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hR.le _)]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume
    (fun x ↦ ‖iteratedFDeriv ℝ j (cutoffSpatialProfile n) x‖) R (hR := hR.le),
    finrank_euclideanSpace_fin, smul_eq_mul, pow_add]
  change R ^ n * R ^ j * ((R ^ n)⁻¹ * cutoffEuclideanDerivMass n j) = _
  field_simp [hR.ne']

/-- `main:lem:smoothing`: dilation of the spatial profile yields the prescribed
frequency dilation, with the dimensional Jacobian cancelling exactly. -/
theorem fourier_cutoffEuclideanKernel (n : ℕ) {R : ℝ} (hR : 0 < R) (ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (cutoffEuclideanKernel n R) ξ = cutoffFrequencyProfile n (R⁻¹ • ξ) := by
  let f : EuclideanSpace ℝ (Fin n) → ℂ := fun x ↦
    Real.fourierChar (-inner ℝ x (R⁻¹ • ξ)) • cutoffSpatialProfile n x
  have hi (x : EuclideanSpace ℝ (Fin n)) :
      Real.fourierChar (-inner ℝ x ξ) • cutoffEuclideanKernel n R x =
        R ^ n • f (R • x) := by
    dsimp [f, cutoffEuclideanKernel]
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
      mul_inv_cancel₀ hR.ne', one_mul]
    exact smul_comm (Real.fourierChar (-inner ℝ x ξ)) (R ^ n)
      (cutoffSpatialProfile n (R • x))
  rw [Real.fourier_eq]
  simp_rw [hi]
  rw [integral_smul, Measure.integral_comp_smul_of_nonneg volume f R (hR := hR.le),
    finrank_euclideanSpace_fin, smul_smul, mul_inv_cancel₀ (pow_ne_zero n hR.ne'), one_smul]
  change 𝓕 (cutoffSpatialProfile n : EuclideanSpace ℝ (Fin n) → ℂ) (R⁻¹ • ξ) = _
  rw [← SchwartzMap.fourier_coe, fourier_cutoffSpatialProfile]

/-- `main:lem:smoothing`: the Euclidean kernel has exactly the Fourier samples
used by the existing periodic cutoff. -/
theorem fourier_cutoffEuclideanKernel_integer (n : ℕ) {R : ℝ} (hR : 0 < R)
    (k : Fin n → ℤ) :
    𝓕 (cutoffEuclideanKernel n R)
      (WithLp.toLp 2 (fun i ↦ (k i : ℝ))) = (periodicCutoffSymbol R k : ℂ) := by
  rw [fourier_cutoffEuclideanKernel n hR, cutoffFrequencyProfile_scaled_integer]

/-- `main:lem:smoothing`: the Euclidean spectrum vanishes outside the very
same finite box defining the periodic kernel. -/
theorem fourier_cutoffEuclideanKernel_eq_zero_of_notMem (n : ℕ) {R : ℝ}
    (hR : 0 < R) {k : Fin n → ℤ} (hk : k ∉ periodicCutoffBox n R) :
    𝓕 (cutoffEuclideanKernel n R) (WithLp.toLp 2 (fun i ↦ (k i : ℝ))) = 0 := by
  rw [fourier_cutoffEuclideanKernel_integer n hR,
    periodicCutoffSymbol_eq_zero_of_notMem hR hk, Complex.ofReal_zero]

/-- `main:eq:smoothing-low`: taking the real part cannot increase the norm
of any derivative of the Euclidean kernel. -/
theorem norm_iteratedFDeriv_re_cutoffEuclideanKernel_le (n j : ℕ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (fun z ↦ (cutoffEuclideanKernel n R z).re) x‖ ≤
      ‖iteratedFDeriv ℝ j (cutoffEuclideanKernel n R) x‖ := by
  have hr : ‖Complex.reCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa using Complex.abs_re_le_norm z
  have hd := Complex.reCLM.iteratedFDeriv_comp_left (x := x)
    (contDiff_cutoffEuclideanKernel n R).contDiffAt (by simp : (j : WithTop ℕ∞) ≤ ∞)
  change ‖iteratedFDeriv ℝ j (Complex.reCLM ∘ cutoffEuclideanKernel n R) x‖ ≤ _
  rw [hd]
  exact (Complex.reCLM.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_of_le_one_left (norm_nonneg _) hr)

/-- `main:eq:smoothing-low`: the real multilinear Euclidean derivative is
integrable, as needed for periodization in its actual real codomain. -/
theorem integrable_iteratedFDeriv_re_cutoffEuclideanKernel (n j : ℕ)
    {R : ℝ} (hR : 0 < R) :
    Integrable (iteratedFDeriv ℝ j (fun z ↦ (cutoffEuclideanKernel n R z).re)) := by
  apply (integrable_norm_iteratedFDeriv_cutoffEuclideanKernel n j hR).mono'
  · exact ((Complex.reCLM.contDiff.comp (contDiff_cutoffEuclideanKernel n R)
      ).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (norm_iteratedFDeriv_re_cutoffEuclideanKernel_le n j R)

/-- `main:eq:smoothing-low`: a uniform Euclidean mass estimate for the real
kernel which will be periodized. No periodic mass bound is assumed here. -/
theorem integral_norm_iteratedFDeriv_re_cutoffEuclideanKernel_le (n j : ℕ)
    {R : ℝ} (hR : 0 < R) :
    (∫ x, ‖iteratedFDeriv ℝ j (fun z ↦ (cutoffEuclideanKernel n R z).re) x‖) ≤
      cutoffEuclideanDerivMass n j * R ^ j := by
  calc
    _ ≤ ∫ x, ‖iteratedFDeriv ℝ j (cutoffEuclideanKernel n R) x‖ :=
      integral_mono (integrable_iteratedFDeriv_re_cutoffEuclideanKernel n j hR).norm
        (integrable_norm_iteratedFDeriv_cutoffEuclideanKernel n j hR)
        (norm_iteratedFDeriv_re_cutoffEuclideanKernel_le n j R)
    _ = _ := integral_norm_iteratedFDeriv_cutoffEuclideanKernel n j hR

end JanetCartan
