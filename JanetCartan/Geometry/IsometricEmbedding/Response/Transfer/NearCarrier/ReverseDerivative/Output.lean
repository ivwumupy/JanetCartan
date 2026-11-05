module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ReverseDerivative.Amplitude

/-!
# The full reverse derivative remainder at fixed frequency

The source-integrated identity for `app:ch_response:eq:direct-envelope-profile`.
This does not yet interchange an output derivative with a frequency integral.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.ReverseDerivative

variable {n r : ℕ}

/-- Pointwise output differentiation retains the second physical amplitude
position (`app:ch_response:eq:direct-envelope-profile`). -/
theorem partialDeriv_oscillation_matrix_output
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (A : FourierIntegral.FullAmplitude n r) (f : Euclidean n → Fin r → ℂ)
    (y x δ : Euclidean n) (j : Fin n)
    (hA : DifferentiableAt ℝ (fun z ↦ A z x δ) y) :
    partialDeriv (fun z ↦ oscillation S ζ ρ z x δ • (A z x δ).mulVec (f x)) y j =
      oscillation S ζ ρ y x δ • (partialDeriv (fun z ↦ A z x δ) y j).mulVec (f x) +
      (oscillation S ζ ρ y x δ * Complex.I * (δ j : ℂ)) • (A y x δ).mulVec (f x) := by
  have he : DifferentiableAt ℝ (fun z ↦ oscillation S ζ ρ z x δ) y := by
    have hi : HasFDerivAt (fun z : Euclidean n ↦ inner ℝ z δ) (innerSL ℝ δ) y := by
      convert (innerSL ℝ δ).hasFDerivAt (x := y) using 1
      ext z
      exact (real_inner_comm z δ).symm
    exact (((Complex.ofRealCLM.hasFDerivAt.comp y
      (hi.sub_const (phaseIncrement S ζ ρ x δ))).const_mul Complex.I).cexp).differentiableAt
  have hm := (matrixAction (r := r)).hasFDerivAt_of_bilinear hA.hasFDerivAt
    (hasFDerivAt_const (f x) y)
  have h := congrArg (fun L : Euclidean n →L[ℝ] (Fin r → ℂ) ↦
    L (EuclideanSpace.single j 1)) (he.hasFDerivAt.smul hm).fderiv
  simp only [add_apply, smul_apply, map_zero, zero_add] at h
  change partialDeriv _ y j =
    oscillation S ζ ρ y x δ • (partialDeriv (fun z ↦ A z x δ) y j).mulVec (f x) +
      partialDeriv (fun z ↦ oscillation S ζ ρ z x δ) y j • (A y x δ).mulVec (f x) at h
  rw [partialDeriv_oscillation_output] at h
  exact h

private theorem integrable_phase_matrix
    (e : Euclidean n → ℂ) (A : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (f : Euclidean n → Fin r → ℂ) (he : Continuous e) (hA : Continuous A)
    (hf : Continuous f) (hs : HasCompactSupport A) :
    Integrable (fun x ↦ e x • (A x).mulVec (f x)) := by
  have hAf : Continuous (fun x ↦ (A x).mulVec (f x)) :=
    ((matrixAction (r := r)).continuous.comp hA).clm_apply hf
  have hcont : Continuous (fun x ↦ e x • (A x).mulVec (f x)) := he.smul hAf
  have hcompact : HasCompactSupport (fun x ↦ e x • (A x).mulVec (f x)) :=
    (hasCompactSupport_matrix_mulVec A f hs).smul_left (f := e)
  exact hcont.integrable_of_hasCompactSupport (μ := (volume : Measure (Euclidean n))) hcompact

/-- Source-integrated output derivative with the exact full remainder
`∂yⱼ A + Σₗ ∂xₗ((B⁻¹)ⱼₗ A)` in
`app:ch_response:eq:direct-envelope-profile`. The only extra integrability input
concerns the output-amplitude derivative; all source terms are integrable by
compact support. Differentiation under the outer integrals remains a separate
domination obligation. -/
theorem integral_output_derivative_transfer
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (y δ : Euclidean n) (j : Fin n)
    (B C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (A : FourierIntegral.FullAmplitude n r) (f : Euclidean n → Fin r → ℂ)
    (hS : ContDiff ℝ ∞ (fun x ↦ phaseIncrement S ζ ρ x δ))
    (hC : ∀ l, ContDiff ℝ ∞ (fun x ↦ C x δ j l))
    (hA : ContDiff ℝ ∞ (fun x ↦ A y x δ))
    (hAy : ∀ x, DifferentiableAt ℝ (fun z ↦ A z x δ) y)
    (hAs : HasCompactSupport (fun x ↦ A y x δ)) (hf : ContDiff ℝ ∞ f)
    (hCB : ∀ x ∈ tsupport (fun x ↦ A y x δ), C x δ * B x δ = 1)
    (hgrad : ∀ x ∈ tsupport (fun x ↦ A y x δ), ∀ l,
      partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x l =
        (B x δ).mulVec (fun k ↦ δ k) l)
    (hyi : Integrable (fun x ↦ oscillation S ζ ρ y x δ •
      (partialDeriv (fun z ↦ A z x δ) y j).mulVec (f x))) :
    (∫ x, partialDeriv (fun z ↦ oscillation S ζ ρ z x δ • (A z x δ).mulVec (f x)) y j) =
      (∑ l, ∫ x, oscillation S ζ ρ y x δ •
        (datumAmplitude C A j l y x δ).mulVec (partialDeriv f x l)) +
      ∫ x, oscillation S ζ ρ y x δ • (remainderAmplitude C A j y x δ).mulVec (f x) := by
  let e := fun x ↦ oscillation S ζ ρ y x δ
  let D := fun l x ↦ datumAmplitude C A j l y x δ
  have he : ContDiff ℝ ∞ e :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.sub hS))).cexp
  have hD (l : Fin n) : ContDiff ℝ ∞ (D l) :=
    (Complex.ofRealCLM.contDiff.comp (hC l)).smul hA
  have hsD (l : Fin n) : HasCompactSupport (D l) := hAs.smul_left (f := fun x ↦ (C x δ j l : ℂ))
  have hiD (l : Fin n) : Integrable (fun x ↦ e x • (D l x).mulVec (partialDeriv f x l)) :=
    integrable_phase_matrix e (D l) _ he.continuous (hD l).continuous
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const) (hsD l)
  have hidD (l : Fin n) : Integrable (fun x ↦ e x • (partialDeriv (D l) x l).mulVec (f x)) :=
    integrable_phase_matrix e _ f he.continuous
      (((hD l).continuous_fderiv (by simp)).clm_apply continuous_const) hf.continuous
      ((hsD l).fderiv_apply ℝ _)
  have hiph : Integrable (fun x ↦ (e x * Complex.I * (δ j : ℂ)) • (A y x δ).mulVec (f x)) :=
    integrable_phase_matrix _ _ f ((he.continuous.mul continuous_const).mul continuous_const)
      hA.continuous hf.continuous hAs
  simp_rw [partialDeriv_oscillation_matrix_output S ζ ρ A f y _ δ j (hAy _)]
  rw [integral_add hyi hiph,
    integral_oscillation_matrix_frequency S ζ ρ y δ j B C A f hS hC hA hAs hf hCB hgrad]
  simp_rw [smul_add]
  rw [show (∑ l, ∫ x, e x • (D l x).mulVec (partialDeriv f x l) +
      e x • (partialDeriv (D l) x l).mulVec (f x)) =
      (∑ l, ∫ x, e x • (D l x).mulVec (partialDeriv f x l)) +
      ∑ l, ∫ x, e x • (partialDeriv (D l) x l).mulVec (f x) by
    simp_rw [integral_add (hiD _) (hidD _)]
    exact Finset.sum_add_distrib]
  simp only [remainderAmplitude, Matrix.add_mulVec, Matrix.sum_mulVec, smul_add,
    Finset.smul_sum]
  rw [integral_add hyi (integrable_finsetSum _ (fun l _ ↦ hidD l)),
    integral_finsetSum _ (fun l _ ↦ hidD l)]
  abel

end JanetCartan.ResponseTransfer.ReverseDerivative
