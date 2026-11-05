module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Exact two-position normal kernels

The change of variables in `app:ch_osc:eq:osc-exact-normal-kernel` is an identity
on the whole kernel, with both physical positions retained. The results here
do not assert the uniform derivative bounds or the operator norm estimate.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.NormalComparison

variable {n r : ℕ}

/-- The averaged phase differential in `app:ch_osc:setup:osc-normal`, in dual
coordinates. Applying it to `x - y` is the pairing with the averaged gradient. -/
def averagedPhaseDifferential (φ : Euclidean n → Euclidean n → ℝ)
    (x y u : Euclidean n) : Euclidean n →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ (fun z ↦ φ z u) (y + t • (x - y))

/-- Convex-segment fundamental theorem of calculus used in the first step of
`app:ch_osc:prop:osc-normal`. The differentiability assumptions are only along
the segment; smoothness on the manuscript's convex neighborhood supplies them. -/
theorem phase_sub_eq_averagedPhaseDifferential
    (φ : Euclidean n → Euclidean n → ℝ) (x y u : Euclidean n)
    (hφ : ∀ t ∈ uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun z ↦ φ z u) (y + t • (x - y)))
    (hint : IntervalIntegrable
      (fun t : ℝ ↦ fderiv ℝ (fun z ↦ φ z u) (y + t • (x - y))) volume 0 1) :
    φ x u - φ y u = averagedPhaseDifferential φ x y u (x - y) := by
  rw [averagedPhaseDifferential, ContinuousLinearMap.intervalIntegral_apply hint]
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ φ (y + t • (x - y)) u)
        (fderiv ℝ (fun z ↦ φ z u) (y + t • (x - y)) (x - y)) t := by
    intro t ht
    simpa only [Function.comp_def, id_eq, one_smul] using (hφ t ht).hasFDerivAt.comp_hasDerivAt t
      (HasDerivAt.const_add y ((hasDerivAt_id t).smul_const (x - y)))
  have hi : IntervalIntegrable
      (fun t : ℝ ↦ fderiv ℝ (fun z ↦ φ z u) (y + t • (x - y)) (x - y)) volume 0 1 :=
    ⟨(ContinuousLinearMap.apply ℝ ℝ (x - y)).integrable_comp hint.1,
      (ContinuousLinearMap.apply ℝ ℝ (x - y)).integrable_comp hint.2⟩
  simpa using (intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi).symm

/-- The exact averaged gradient of `app:ch_osc:setup:osc-normal`. -/
def averagedGradient (φ : Euclidean n → Euclidean n → ℝ)
    (x y u : Euclidean n) : Euclidean n :=
  (InnerProductSpace.toDual ℝ (Euclidean n)).symm (averagedPhaseDifferential φ x y u)

/-- The dual-coordinate definition agrees with the integral of gradients in
`app:ch_osc:setup:osc-normal`. -/
theorem averagedGradient_eq_integral_gradient
    (φ : Euclidean n → Euclidean n → ℝ) (x y u : Euclidean n)
    (hint : IntervalIntegrable
      (fun t : ℝ ↦ fderiv ℝ (fun z ↦ φ z u) (y + t • (x - y))) volume 0 1) :
    averagedGradient φ x y u =
      ∫ t in (0 : ℝ)..1, gradient (fun z ↦ φ z u) (y + t • (x - y)) := by
  exact ((InnerProductSpace.toDual ℝ (Euclidean n)).symm.toContinuousLinearEquiv.toContinuousLinearMap.intervalIntegral_comp_comm hint).symm

/-- Exact phase linearization, not an asymptotic expansion; first step of
`app:ch_osc:prop:osc-normal`. -/
theorem phase_sub_eq_inner_averagedGradient
    (φ : Euclidean n → Euclidean n → ℝ) (x y u : Euclidean n)
    (hφ : ∀ t ∈ uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun z ↦ φ z u) (y + t • (x - y)))
    (hint : IntervalIntegrable
      (fun t : ℝ ↦ fderiv ℝ (fun z ↦ φ z u) (y + t • (x - y))) volume 0 1) :
    φ x u - φ y u = inner ℝ (x - y) (averagedGradient φ x y u) := by
  rw [real_inner_comm, averagedGradient, InnerProductSpace.toDual_symm_apply]
  exact phase_sub_eq_averagedPhaseDifferential φ x y u hφ hint

/-- The full matrix amplitude `a(x,u) a(y,u)*` in
`app:ch_osc:prop:osc-normal`, without restricting to the diagonal. -/
def normalAmplitude (a : Euclidean n → Euclidean n → Fin r → ℂ)
    (x y u : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  fun i j ↦ a x u i * star (a y u j)

/-- The exact oscillatory factor, with the manuscript's radian frequency `K`.
The associated Fourier prefactor is `(K / (2 * π)) ^ n`. -/
def oscillatoryFactor (K θ : ℝ) : ℂ := Complex.exp (Complex.I * (K * θ : ℝ))

/-- The complete masked kernel before substitution in
`app:ch_osc:eq:osc-exact-normal-kernel`. -/
def maskedNormalKernel (D : Set (Euclidean n)) (K : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ)
    (a : Euclidean n → Euclidean n → Fin r → ℂ) (m : Euclidean n → ℝ)
    (x y : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  (K / (2 * Real.pi)) ^ n •
    ∫ u in D, oscillatoryFactor K (φ x u - φ y u) • (m u • normalAmplitude a x y u)

/-- Jacobian division for an injective differentiable chart. This is the
substitution underlying `app:ch_osc:eq:osc-exact-normal-kernel`; it is valid for
Bochner integrals, so it applies to the entire matrix amplitude at once. -/
theorem integral_eq_inverse_jacobian_integral
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : Set (Euclidean n)) (hD : MeasurableSet D)
    (Ψ U : Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (hΨ : ∀ u ∈ D, HasFDerivWithinAt Ψ (J u) D u)
    (hinj : InjOn Ψ D) (hU : ∀ u ∈ D, U (Ψ u) = u)
    (hJ : ∀ u ∈ D, (J u).det ≠ 0) (B : Euclidean n → F) :
    (∫ u in D, B u) = ∫ v in Ψ '' D, |(J (U v)).det|⁻¹ • B (U v) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hD hΨ hinj]
  apply setIntegral_congr_fun hD
  intro u hu
  simp only [hU u hu, smul_smul, mul_inv_cancel₀ (abs_ne_zero.mpr (hJ u hu)), one_smul]

/-- The transformed amplitude in `app:ch_osc:eq:osc-exact-normal-kernel`.
The inverse `U` and Jacobian `J` may depend on both positions and on the parameter;
here those variables are fixed, never identified with each other. -/
def inverseJacobianAmplitude
    (a : Euclidean n → Euclidean n → Fin r → ℂ) (m : Euclidean n → ℝ)
    (x y : Euclidean n) (U : Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (v : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  |(J (U v)).det|⁻¹ • (m (U v) • normalAmplitude a x y (U v))

/-- Exact full-kernel substitution from `app:ch_osc:eq:osc-exact-normal-kernel`.
The phase identity is supplied separately by the segment FTC. No diagonal
restriction or discarded Jacobian is used. -/
theorem maskedNormalKernel_eq_integral_image
    (D : Set (Euclidean n)) (hD : MeasurableSet D) (K : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ)
    (a : Euclidean n → Euclidean n → Fin r → ℂ) (m : Euclidean n → ℝ)
    (x y : Euclidean n) (Ψ U : Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (hΨ : ∀ u ∈ D, HasFDerivWithinAt Ψ (J u) D u)
    (hinj : InjOn Ψ D) (hU : ∀ u ∈ D, U (Ψ u) = u)
    (hJ : ∀ u ∈ D, (J u).det ≠ 0)
    (hphase : ∀ u ∈ D, φ x u - φ y u = inner ℝ (x - y) (Ψ u)) :
    maskedNormalKernel D K φ a m x y =
      (K / (2 * Real.pi)) ^ n • ∫ v in Ψ '' D,
        oscillatoryFactor K (inner ℝ (x - y) v) •
          inverseJacobianAmplitude a m x y U J v := by
  unfold maskedNormalKernel
  congr 1
  rw [integral_eq_inverse_jacobian_integral D hD Ψ U J hΨ hinj hU hJ]
  apply setIntegral_congr_fun (measurable_image_of_fderivWithin hD hΨ hinj)
  rintro v ⟨u, hu, rfl⟩
  simp only [inverseJacobianAmplitude, hU u hu, hphase u hu]
  exact smul_comm _ _ _

/-- Whole-space form of `app:ch_osc:eq:osc-exact-normal-kernel`, with literal
zero extension off the chart image. Smoothness of that extension is a separate
consequence of the buffered support hypothesis, not asserted here. -/
theorem maskedNormalKernel_eq_integral_zeroExtension
    (D : Set (Euclidean n)) (hD : MeasurableSet D) (K : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ)
    (a : Euclidean n → Euclidean n → Fin r → ℂ) (m : Euclidean n → ℝ)
    (x y : Euclidean n) (Ψ U : Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (hΨ : ∀ u ∈ D, HasFDerivWithinAt Ψ (J u) D u)
    (hinj : InjOn Ψ D) (hU : ∀ u ∈ D, U (Ψ u) = u)
    (hJ : ∀ u ∈ D, (J u).det ≠ 0)
    (hphase : ∀ u ∈ D, φ x u - φ y u = inner ℝ (x - y) (Ψ u)) :
    maskedNormalKernel D K φ a m x y =
      (K / (2 * Real.pi)) ^ n • ∫ v,
        oscillatoryFactor K (inner ℝ (x - y) v) •
          (Ψ '' D).indicator (inverseJacobianAmplitude a m x y U J) v := by
  rw [maskedNormalKernel_eq_integral_image D hD K φ a m x y Ψ U J hΨ hinj hU hJ hphase,
    ← integral_indicator (measurable_image_of_fderivWithin hD hΨ hinj)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  by_cases hv : v ∈ Ψ '' D <;> simp [hv]

/-- The exact normal-kernel formula with the actual averaged phase gradient,
as in `app:ch_osc:eq:osc-exact-normal-kernel`. The Jacobian gap and the inverse
are precisely the chart inputs; the phase identity is proved, not assumed. -/
theorem maskedNormalKernel_eq_averagedGradient_integral
    (D : Set (Euclidean n)) (hD : MeasurableSet D) (K : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ)
    (a : Euclidean n → Euclidean n → Fin r → ℂ) (m : Euclidean n → ℝ)
    (x y : Euclidean n) (U : Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (hφ : ∀ u ∈ D, ∀ t ∈ uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun z ↦ φ z u) (y + t • (x - y)))
    (hint : ∀ u ∈ D, IntervalIntegrable
      (fun t : ℝ ↦ fderiv ℝ (fun z ↦ φ z u) (y + t • (x - y))) volume 0 1)
    (hΨ : ∀ u ∈ D, HasFDerivWithinAt (averagedGradient φ x y) (J u) D u)
    (hinj : InjOn (averagedGradient φ x y) D)
    (hU : ∀ u ∈ D, U (averagedGradient φ x y u) = u)
    {c : ℝ} (hc : 0 < c) (hgap : ∀ u ∈ D, c ≤ |(J u).det|) :
    maskedNormalKernel D K φ a m x y =
      (K / (2 * Real.pi)) ^ n • ∫ v,
        oscillatoryFactor K (inner ℝ (x - y) v) •
          ((averagedGradient φ x y) '' D).indicator
            (inverseJacobianAmplitude a m x y U J) v := by
  apply maskedNormalKernel_eq_integral_zeroExtension D hD K φ a m x y
    (averagedGradient φ x y) U J hΨ hinj hU
  · intro u hu
    exact abs_pos.mp (hc.trans_le (hgap u hu))
  · intro u hu
    exact phase_sub_eq_inner_averagedGradient φ x y u (hφ u hu) (hint u hu)

end JanetCartan.NormalComparison
