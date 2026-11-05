module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.DifferentialFactors.SourceAction

/-!
# Output differentiation of the unregularized image composite

For `app:ch_background:prop:bg-frame`, Step 1, Fourier inversion on the
actual Schwartz output justifies the `+i 2πξ` factor. The source square is
differentiated literally, giving the entire coefficient `Q`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff
open JanetCartan.Pseudodifferential
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem partialDeriv_schwartz_fourierInv (v : 𝓢(E, ℂ)) (x : E) (a : Fin d) :
    partialDeriv (v : E → ℂ) x a =
      𝓕⁻ (fun ξ ↦ Complex.I * (((2 * Real.pi) • ξ) a : ℝ) * (𝓕 v : 𝓢(E, ℂ)) ξ) x := by
  have h := congrArg (fun w : 𝓢(E, ℂ) ↦ (𝓕⁻ w : 𝓢(E, ℂ)) x)
    (SchwartzMap.fourier_lineDerivOp_eq v (EuclideanSpace.single a 1))
  rw [FourierTransform.fourierInv_fourier_eq, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.fourierInv_coe] at h
  have ht : (fun ξ : E ↦ inner ℝ ξ (EuclideanSpace.single a 1)).HasTemperateGrowth := by
    fun_prop
  change partialDeriv (v : E → ℂ) x a = _ at h
  rw [h]
  apply congrArg (fun f : E → ℂ ↦ 𝓕⁻ f x)
  funext ξ
  change (2 * Real.pi * Complex.I) •
    (SchwartzMap.smulLeftCLM ℂ (fun ξ : E ↦ inner ℝ ξ (EuclideanSpace.single a 1)) (𝓕 v)) ξ = _
  rw [SchwartzMap.smulLeftCLM_apply_apply ht]
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul,
    PiLp.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

variable {I J : Type} [Fintype I] [Fintype J]

omit [Fintype I] in
/-- Differentiation of a source-multiplied Schwartz field in the actual
coefficient operator, with the complete `Q = A dC + ZC` coefficient
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientOperator_source_schwartz
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (C : E → ℝ) (w : J → 𝓢(E, ℂ)) (x : E) (hC : DifferentiableAt ℝ C x) (i : I) :
    coefficientOperator A Z (fun z j ↦ (C z : ℂ) * w j z) x i =
      (∑ a, ∑ j, (A x a i j : ℂ) * C x *
        𝓕⁻ (fun ξ ↦ Complex.I * (((2 * Real.pi) • ξ) a : ℝ) *
          (𝓕 (w j) : 𝓢(E, ℂ)) ξ) x) +
      ∑ j, (sourceProductCoefficient A Z C x i j : ℂ) * w j x := by
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hC.hasFDerivAt
  have hd a j : partialDeriv (fun z ↦ (C z : ℂ) * w j z) x a =
      ((partialDeriv C x a : ℝ) : ℂ) * w j x + (C x : ℂ) * partialDeriv (w j : E → ℂ) x a := by
    have hm := hc.mul (w j).differentiableAt.hasFDerivAt
    change HasFDerivAt (fun z ↦ (C z : ℂ) * w j z) _ x at hm
    rw [partialDeriv, hm.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Function.comp_apply, partialDeriv]
    ring
  unfold coefficientOperator
  simp_rw [hd, partialDeriv_schwartz_fourierInv]
  simp only [sourceProductCoefficient, Complex.ofReal_add, Complex.ofReal_sum,
    Complex.ofReal_mul, add_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  simp only [← mul_assoc]
  rw [Finset.sum_comm (f := fun a j ↦ (A x a i j : ℂ) *
    ((partialDeriv C x a : ℝ) : ℂ) * w j x)]
  simp only [mul_assoc]
  ring

omit [Fintype J] in
/-- Actual Fourier derivative of `J² P* v`, with the physical frequency
factor justified by Schwartz inversion (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem partialDeriv_imageBesselSquared_coefficientAdjointSchwartz
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (v : E → I → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ v x i)) (x : E) (j : J) (a : Fin d) :
    partialDeriv (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ))
      (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ))
        (coefficientAdjointSchwartz A Z v hA hZ hv hc j)) : E → ℂ) x a =
      𝓕⁻ (fun ξ ↦ Complex.I * (((2 * Real.pi) • ξ) a : ℝ) *
        (((1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ : ℝ) *
          differentialAdjointSourceTransform A Z v ξ j)) x := by
  rw [partialDeriv_schwartz_fourierInv]
  apply congrArg (fun f : E → ℂ ↦ 𝓕⁻ f x)
  funext ξ
  rw [fourier_imageBesselMultiplier, fourier_imageBesselMultiplier]
  have hf : (𝓕 (coefficientAdjointSchwartz A Z v hA hZ hv hc j) : 𝓢(E, ℂ)) ξ =
      differentialAdjointSourceTransform A Z v ξ j :=
    fourier_coefficientFormalAdjoint A Z v hA hZ hv hc ξ j
  rw [hf, ← mul_assoc (imageBesselSymbol ξ : ℂ), ← Complex.ofReal_mul, imageBesselSymbol_sq]

/-- All output derivatives of the literal masked composite have been
performed. This source-first formula retains both masks, the complete `Q`,
and the two opposite Fourier phase factors. Combining its finite sums into
the matrix full-amplitude operator is the next assembly step
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientImageNormal_eq_frequency_factors
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (χ μ : E → ℝ) (v : E → I → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i)) (x : E) (i : I) :
    coefficientImageNormal A Z χ μ v hA hZ hμ hμc hv x i =
      (μ x : ℂ) *
        ((∑ a, ∑ j, (A x a i j : ℂ) * χ x ^ 2 *
          𝓕⁻ (fun ξ ↦ Complex.I * (((2 * Real.pi) • ξ) a : ℝ) *
            (((1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ : ℝ) *
              differentialAdjointSourceTransform A Z (fun y l ↦ (μ y : ℂ) * v y l) ξ j)) x) +
        ∑ j, (sourceProductCoefficient A Z (fun z ↦ χ z ^ 2) x i j : ℂ) *
          𝓕⁻ (fun ξ ↦ ((1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ : ℝ) *
            differentialAdjointSourceTransform A Z (fun y l ↦ (μ y : ℂ) * v y l) ξ j) x) := by
  have hm (l : I) : ContDiff ℝ ∞ (fun y ↦ (μ y : ℂ) * v y l) :=
    (Complex.ofRealCLM.contDiff.comp hμ).mul (hv l)
  have hmc (l : I) : HasCompactSupport (fun y ↦ (μ y : ℂ) * v y l) :=
    (hμc.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)).mul_right
  unfold coefficientImageNormal
  rw [coefficientOperator_source_schwartz A Z _ _ x ((hχ.pow 2).differentiable (by simp) x)]
  simp only [Complex.ofReal_pow]
  apply congrArg ((μ x : ℂ) * ·)
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply congrArg (fun f : E → ℂ ↦ 𝓕⁻ f x)
    funext ξ
    rw [fourier_imageBesselMultiplier, fourier_imageBesselMultiplier]
    have hf : (𝓕 (coefficientAdjointSchwartz A Z (fun y l ↦ (μ y : ℂ) * v y l)
        hA hZ hm hmc j) : 𝓢(E, ℂ)) ξ =
        differentialAdjointSourceTransform A Z (fun y l ↦ (μ y : ℂ) * v y l) ξ j :=
      fourier_coefficientFormalAdjoint A Z _ hA hZ hm hmc ξ j
    rw [hf, ← mul_assoc (imageBesselSymbol ξ : ℂ), ← Complex.ofReal_mul, imageBesselSymbol_sq]
  · apply Finset.sum_congr rfl
    intro j _
    rw [imageBesselSquared_coefficientAdjointSchwartz]

end JanetCartan.ContinuumNormalReduction.ImageNormal
