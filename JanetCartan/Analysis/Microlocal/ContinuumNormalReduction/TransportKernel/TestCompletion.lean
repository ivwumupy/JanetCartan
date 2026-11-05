module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Completion
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.GlobalSmooth
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.FrequencyTransfer.Algebra

/-!
# Completion of the source-tested transport operator

For the bounded-frequency error after `app:ch_background:eq:bg-real-symbol`,
compact frequency support and compact source support justify Fubini. The actual
source-tested operator splits into its completed amplitude and the literal
correction kernel. Only convergence of the original source Fourier transform
is assumed; convergence of the correction and completed transforms is proved.
All physical integrals here use Euclidean Lebesgue measure. No identification
with a torus output measure is asserted.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction Pseudodifferential
variable {n N : ℕ}

section Completion
variable (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))

/-- The completion discrepancy in the Fourier convention `k = 2πξ`
(`app:ch_background:eq:bg-symbol`). -/
def unitCompletionErrorEntry (i j : Fin n) (x y ξ : Euclidean n) : ℂ :=
  reflectedCompletionError a J u Ω K (x, y, (2 * Real.pi) • ξ) i j

/-- The completed reflected amplitude in the same Fourier convention
(`app:ch_background:eq:bg-real-symbol`). -/
def unitCompletedReflectedEntry (i j : Fin n) (x y ξ : Euclidean n) : ℂ :=
  completedReflectedAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j

variable (he : ContDiff ℝ ∞ (reflectedCompletionError a J u Ω K))
    (hhigh : ∀ t : ℝ, 2 ≤ t → a.high t = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)

include he hhigh hC hcomparison

/-- Joint absolute integrability of the actual completion discrepancy against
a compact continuous source test. Its frequency radius is divided by `2π`;
there is no unproved Fourier integrability premise for this term
(`app:ch_background:eq:bg-symbol`). -/
theorem integrable_unitCompletionErrorEntry_test (i j : Fin n)
    (f : Euclidean n → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : Euclidean n) :
    Integrable (fun p : Euclidean n × Euclidean n ↦
      f p.2 • unitCompletionErrorEntry a J u Ω K i j x p.2 p.1) := by
  have hc : Continuous (fun p : Euclidean n × Euclidean n ↦
      unitCompletionErrorEntry a J u Ω K i j x p.2 p.1) :=
    Complex.continuous_ofReal.comp (((realMatrixEntry i j).continuous.comp he.continuous).comp
      (continuous_const.prodMk (continuous_snd.prodMk
        (continuous_fst.const_smul (2 * Real.pi)))))
  apply ((hf.comp continuous_snd).smul hc).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro
    ((isCompact_closedBall (0 : Euclidean n) (max 2 (2 * C) / (2 * Real.pi))).prod hfc.isCompact)
  intro p hp
  by_cases hξ : p.1 ∈ Metric.closedBall (0 : Euclidean n) (max 2 (2 * C) / (2 * Real.pi))
  · have hy : p.2 ∉ tsupport f := fun hy ↦ hp ⟨hξ, hy⟩
    simp [image_eq_zero_of_notMem_tsupport hy]
  · have hξ' : max 2 (2 * C) < ‖(2 * Real.pi) • p.1‖ := by
      have hp' : max 2 (2 * C) / (2 * Real.pi) < ‖p.1‖ := by simpa using hξ
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      nlinarith [(div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hp']
    simp [unitCompletionErrorEntry, reflectedCompletionError_eq_zero_of_large_frequency
      a J u Ω K hhigh hC hcomparison (x, p.2, (2 * Real.pi) • p.1) hξ'.le]

/-- The correction's source Fourier transform is absolutely integrable by
Fubini and the unit modulus of the Fourier phase
(`app:ch_background:eq:bg-symbol`). -/
theorem integrable_sourceAmplitudeTransform_completionError (i j : Fin n)
    (f : Euclidean n → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : Euclidean n) :
    Integrable (sourceAmplitudeTransform (unitCompletionErrorEntry a J u Ω K i j) f x) := by
  have hi := integrable_unitCompletionErrorEntry_test a J u Ω K he hhigh hC hcomparison
    i j f hf hfc x
  have hp : Continuous (fun p : Euclidean n × Euclidean n ↦
      Real.fourierChar (-inner ℝ p.2 p.1)) := by fun_prop
  have hphase : Integrable (fun p : Euclidean n × Euclidean n ↦
      Real.fourierChar (-inner ℝ p.2 p.1) •
        (f p.2 • unitCompletionErrorEntry a J u Ω K i j x p.2 p.1)) := by
    apply hi.norm.mono' (hp.aestronglyMeasurable.smul hi.aestronglyMeasurable)
    filter_upwards [] with p
    exact le_of_eq (Circle.norm_smul _ _)
  unfold sourceAmplitudeTransform
  simpa only [Real.fourier_eq] using hphase.integral_prod_left

/-- Fubini identifies the source-tested discrepancy operator with the literal
normalized correction kernel. No separate kernel-action input is assumed
(`app:ch_background:eq:bg-symbol`). -/
theorem fullAmplitudeOperator_completionError_eq_kernel (i j : Fin n)
    (f : Euclidean n → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : Euclidean n) :
    fullAmplitudeOperator (unitCompletionErrorEntry a J u Ω K i j) f x =
      ∫ y, f y * completionErrorKernel a J u Ω K i j x y := by
  rw [fullAmplitudeOperator_eq_integral_amplitudeKernel _ f x
    (integrable_unitCompletionErrorEntry_test a J u Ω K he hhigh hC hcomparison
      i j f hf hfc x)]
  simp only [completionErrorKernel_eq_amplitudeKernel, smul_eq_mul]
  rfl

/-- The correction kernel is absolutely integrable against the same tests;
this is the actual source integral occurring in the completed operator
(`app:ch_background:eq:bg-symbol`). -/
theorem integrable_completionErrorKernel_test (i j : Fin n)
    (f : Euclidean n → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : Euclidean n) :
    Integrable (fun y ↦ f y * completionErrorKernel a J u Ω K i j x y) := by
  simp_rw [completionErrorKernel_eq_amplitudeKernel]
  exact integrable_amplitudeKernel_test (unitCompletionErrorEntry a J u Ω K i j) f x
      (integrable_unitCompletionErrorEntry_test a J u Ω K he hhigh hC hcomparison
        i j f hf hfc x)

omit hhigh hC hcomparison in
/-- Source integration respects the actual completion decomposition. Both
amplitudes are evaluated at the same `2πξ`, with no angular symmetry
assumption (`app:ch_background:eq:bg-real-symbol`). -/
theorem sourceAmplitudeTransform_reflected_eq_completed_add_error
    (hc : ContDiff ℝ ∞ (completedReflectedAmplitude a J u Ω K))
    (i j : Fin n) (f : Euclidean n → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (x ξ : Euclidean n) :
    sourceAmplitudeTransform (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x ξ =
      sourceAmplitudeTransform (unitCompletedReflectedEntry a J u Ω K i j) f x ξ +
      sourceAmplitudeTransform (unitCompletionErrorEntry a J u Ω K i j) f x ξ := by
  have hid : (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) =
      (fun x y ξ ↦ unitCompletedReflectedEntry a J u Ω K i j x y ξ +
        unitCompletionErrorEntry a J u Ω K i j x y ξ) := by
    funext x y ξ
    simp [unitCompletedReflectedEntry, unitCompletionErrorEntry, reflectedCompletionError]
  rw [hid]
  apply sourceAmplitudeTransform_add_of_compactSupport _ _ f x ξ hf hfc
  · exact Complex.continuous_ofReal.comp (((realMatrixEntry i j).continuous.comp hc.continuous).comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const)))
  · exact Complex.continuous_ofReal.comp (((realMatrixEntry i j).continuous.comp he.continuous).comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const)))

/-- Completion preserves convergence of the source Fourier integral: the
original transform is the completed transform plus an integrable bounded-
frequency discrepancy. Thus no new convergence hypothesis is introduced
(`app:ch_background:eq:bg-symbol`). -/
theorem integrable_sourceAmplitudeTransform_completed
    (hc : ContDiff ℝ ∞ (completedReflectedAmplitude a J u Ω K))
    (i j : Fin n) (f : Euclidean n → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (x : Euclidean n)
    (hi : Integrable (sourceAmplitudeTransform (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x)) :
    Integrable (sourceAmplitudeTransform (unitCompletedReflectedEntry a J u Ω K i j) f x) := by
  have hie := integrable_sourceAmplitudeTransform_completionError a J u Ω K he hhigh hC
    hcomparison i j f hf hfc x
  apply (hi.sub hie).congr
  filter_upwards [] with ξ
  dsimp only [Pi.sub_apply]
  rw [sourceAmplitudeTransform_reflected_eq_completed_add_error a J u Ω K he hc
    i j f hf hfc x ξ, add_sub_cancel_right]

/-- Exact source-tested completion of the transport operator. The error is
its actual Lebesgue kernel, and its absolute integrability is proved above.
The only convergence premise is on the original unregularized source
transform; no bounded unregularized carrier is assumed
(`app:ch_background:eq:bg-symbol`, `app:ch_background:eq:bg-real-symbol`). -/
theorem fullAmplitudeOperator_reflected_eq_completed_add_kernel
    (hc : ContDiff ℝ ∞ (completedReflectedAmplitude a J u Ω K))
    (i j : Fin n) (f : Euclidean n → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (x : Euclidean n)
    (hi : Integrable (sourceAmplitudeTransform (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x)) :
    fullAmplitudeOperator (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x =
      fullAmplitudeOperator (unitCompletedReflectedEntry a J u Ω K i j) f x +
        ∫ y, f y * completionErrorKernel a J u Ω K i j x y := by
  rw [← fullAmplitudeOperator_completionError_eq_kernel a J u Ω K he hhigh hC hcomparison
    i j f hf hfc x]
  have hic := integrable_sourceAmplitudeTransform_completed a J u Ω K he hhigh hC hcomparison
    hc i j f hf hfc x hi
  have hie := integrable_sourceAmplitudeTransform_completionError a J u Ω K he hhigh hC
    hcomparison i j f hf hfc x
  have hinv {g : Euclidean n → ℂ} (hg : Integrable g) :
      Integrable (fun ξ ↦ Real.fourierChar (inner ℝ ξ x) • g ξ) := by
    simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (-x)).mpr hg
  simp only [fullAmplitudeOperator, Real.fourierInv_eq]
  simp_rw [sourceAmplitudeTransform_reflected_eq_completed_add_error a J u Ω K he hc
    i j f hf hfc x, smul_add]
  exact integral_add (hinv hic) (hinv hie)

end Completion

/-- Primitive chart regularity and the conic support buffer supply every
smoothness input in the exact completed-operator identity. The remaining
analytic premise is convergence of the original source Fourier transform on
this compact source test; its actual producer is the shared source-decay
calculus. The original output measure is not transported. This is the
bounded-frequency decomposition used after `app:ch_background:eq:bg-symbol`.
-/
theorem fullAmplitudeOperator_completion_of_primitive_inputs
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (F : TransportSymbol.InputVariables n → TransportSymbol.Variables n × Euclidean 2)
    {Ω : Set (TransportSymbol.Variables n × Euclidean 2)}
    {W Z : Set (TransportSymbol.InputVariables n)}
    (hΩ : IsOpen Ω) (h : TransportSymbol.PrimitiveRegularity a J W)
    (hu : ContDiffOn ℝ ∞ u Ω)
    (hmap : MapsTo (TransportSymbol.inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, F (TransportSymbol.inverseCoordinates u p) = p)
    (hs : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z)
    (hbuffer : closure (F '' Z) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω)
    (hzero : ∀ t : ℝ, t ≤ 1 → a.high t = 0)
    (hone : ∀ t : ℝ, 2 ≤ t → a.high t = 1)
    {Cupper Clower ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hClower : 0 < Clower)
    (hℓ : 0 < ℓ) (hlow : Cupper * ℓ ≤ 1)
    (hupper : ∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖)
    (hlower : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ Clower * ‖(u p).2‖)
    {K : Set (Euclidean 2)} (hK : IsCompact K)
    (i j : Fin n) (f : Euclidean n → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (x : Euclidean n)
    (hi : Integrable (sourceAmplitudeTransform (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x)) :
    fullAmplitudeOperator (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x =
      fullAmplitudeOperator (unitCompletedReflectedEntry a J u Ω K i j) f x +
        ∫ y, f y * completionErrorKernel a J u Ω K i j x y := by
  have ha := (TransportSymbol.amplitude_smooth_and_derivatives_of_punctured_buffer
    a J u F hΩ h hu hmap hright hs hbuffer hzero hCupper hℓ hlow hupper hK).1
  have hh := TransportSymbol.homogeneousAmplitude_contDiffOn_punctured
    a J u F hΩ h hu hmap hright hs hbuffer hK
  exact fullAmplitudeOperator_reflected_eq_completed_add_kernel a J u Ω K
    (reflectedCompletionError_contDiff a J u Ω K ha hh) hone hClower hlower
    (completedReflectedAmplitude_contDiff a J u Ω K hh) i j f hf hfc x hi

end JanetCartan.ContinuumRow.TransportKernel
