module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.DifferentialFactors.OutputAction

/-!
# Actual matrix amplitude of the Euclidean image normal

For `app:ch_background:prop:bg-frame`, Step 1, combine the previously checked
source integration by parts and output differentiation into the literal
`matrixFullAmplitudeOperator`. The finite matrix sums are interchanged only
after proving absolute frequency convergence of each source-tested entry.
These identities are consumed by the parent image-normal diagonal reduction;
the explicit remainder is controlled by `DifferentialFactors.PrimitiveBounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff
open JanetCartan.Pseudodifferential
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Mat" => Matrix (Fin d) (Fin d) ℝ

private theorem fourier_sum_integrable {ι : Type} [Fintype ι]
    (f : ι → E → ℂ) (hf : ∀ i, Integrable (f i)) (ξ : E) :
    𝓕 (fun y ↦ ∑ i, f i y) ξ = ∑ i, 𝓕 (f i) ξ := by
  simp only [Real.fourier_eq, Finset.smul_sum]
  exact integral_finsetSum _ (fun i _ ↦ (Real.fourierIntegral_convergent_iff ξ).2 (hf i))

private theorem fourier_const_mul (c : ℂ) (f : E → ℂ) (ξ : E) :
    𝓕 (fun y ↦ c * f y) ξ = c * 𝓕 f ξ := by
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  simp_rw [mul_left_comm _ c]
  exact integral_const_mul _ _

private theorem fourierInv_sum_integrable {ι : Type} [Fintype ι]
    (f : ι → E → ℂ) (hf : ∀ i, Integrable (f i)) (x : E) :
    𝓕⁻ (fun ξ ↦ ∑ i, f i ξ) x = ∑ i, 𝓕⁻ (f i) x := by
  simp only [Real.fourierInv_eq, Finset.smul_sum]
  apply integral_finsetSum
  intro i _
  simpa only [inner_neg_right, neg_neg] using
    (Real.fourierIntegral_convergent_iff (-x)).2 (hf i)

private theorem fourierInv_const_mul (c : ℂ) (f : E → ℂ) (x : E) :
    𝓕⁻ (fun ξ ↦ c * f ξ) x = c * 𝓕⁻ f x := by
  simp only [Real.fourierInv_eq, Circle.smul_def, smul_eq_mul]
  simp_rw [mul_left_comm _ c]
  exact integral_const_mul _ _

private theorem fourierInv_add_integrable (f g : E → ℂ)
    (hf : Integrable f) (hg : Integrable g) (x : E) :
    𝓕⁻ (fun ξ ↦ f ξ + g ξ) x = 𝓕⁻ f x + 𝓕⁻ g x := by
  simp only [Real.fourierInv_eq, smul_add]
  apply integral_add
  · simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (-x)).2 hf
  · simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (-x)).2 hg

private theorem integrable_frequency_derivative {I J : Type} [Fintype I]
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (v : E → I → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun y ↦ A y a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun y ↦ Z y i j))
    (hv : ∀ i, ContDiff ℝ ∞ (fun y ↦ v y i))
    (hc : ∀ i, HasCompactSupport (fun y ↦ v y i)) (j : J) (a : Fin d) :
    Integrable (fun ξ ↦ Complex.I * (((2 * Real.pi) • ξ) a : ℝ) *
      (((1 + ‖(2 * Real.pi) • ξ‖^2)⁻¹ : ℝ) * differentialAdjointSourceTransform A Z v ξ j)) := by
  let w := coefficientAdjointSchwartz A Z v hA hZ hv hc j
  let t := SchwartzMap.smulLeftCLM ℂ (fun ξ : E ↦ Complex.I * (((2 * Real.pi) • ξ) a : ℝ))
    (𝓕 (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ))
      (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) w)))
  have hp : (fun ξ : E ↦ Complex.I * (((2 * Real.pi) • ξ) a : ℝ)).HasTemperateGrowth := by
    have hh : (fun ξ : E ↦ inner ℝ ξ (EuclideanSpace.single a 1)).HasTemperateGrowth := by
      fun_prop
    have he : (fun ξ : E ↦ ξ a).HasTemperateGrowth := by
      simpa only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] using hh
    simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    fun_prop
  have ht : (t : E → ℂ) = (fun ξ ↦ Complex.I * (((2 * Real.pi) • ξ) a : ℝ) *
      (((1 + ‖(2 * Real.pi) • ξ‖^2)⁻¹ : ℝ) * differentialAdjointSourceTransform A Z v ξ j)) := by
    funext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply hp]
    simp only [smul_eq_mul, fourier_imageBesselMultiplier]
    have hf : (𝓕 w : 𝓢(E, ℂ)) ξ = differentialAdjointSourceTransform A Z v ξ j :=
      fourier_coefficientFormalAdjoint A Z v hA hZ hv hc ξ j
    rw [hf, ← mul_assoc (imageBesselSymbol ξ : ℂ), ← Complex.ofReal_mul, imageBesselSymbol_sq]
  rw [← ht]
  exact t.integrable

private def outputFrequency (A : E → Fin d → Mat) (Z : E → Mat)
    (C μ : E → ℝ) (x : E) (i : Fin d) (S : E → Fin d → ℂ) (ξ : E) : ℂ :=
  (μ x : ℂ) * ((∑ a, ∑ j, (A x a i j : ℂ) * C x *
    (Complex.I * (((2 * Real.pi) • ξ) a : ℝ) *
      (((1 + ‖(2 * Real.pi) • ξ‖^2)⁻¹ : ℝ) * S ξ j))) +
    ∑ j, (sourceProductCoefficient A Z C x i j : ℂ) *
      (((1 + ‖(2 * Real.pi) • ξ‖^2)⁻¹ : ℝ) * S ξ j))

private theorem integrable_outputFrequency (A : E → Fin d → Mat) (Z : E → Mat)
    (C μ : E → ℝ) (x : E) (i : Fin d) (S : E → Fin d → ℂ)
    (hS : ∀ j, Integrable (fun ξ ↦ ((1 + ‖(2 * Real.pi) • ξ‖^2)⁻¹ : ℝ) * S ξ j))
    (hD : ∀ a j, Integrable (fun ξ ↦ Complex.I * (((2 * Real.pi) • ξ) a : ℝ) *
      (((1 + ‖(2 * Real.pi) • ξ‖^2)⁻¹ : ℝ) * S ξ j))) :
    Integrable (outputFrequency A Z C μ x i S) :=
  ((integrable_finsetSum _ (fun a _ ↦ integrable_finsetSum _ (fun j _ ↦
    (hD a j).const_mul _))).add
      (integrable_finsetSum _ (fun j _ ↦ (hS j).const_mul _))).const_mul _

private theorem fourierInv_outputFrequency (A : E → Fin d → Mat) (Z : E → Mat)
    (C μ : E → ℝ) (x : E) (i : Fin d) (S : E → Fin d → ℂ)
    (hS : ∀ j, Integrable (fun ξ ↦ ((1 + ‖(2 * Real.pi) • ξ‖^2)⁻¹ : ℝ) * S ξ j))
    (hD : ∀ a j, Integrable (fun ξ ↦ Complex.I * (((2 * Real.pi) • ξ) a : ℝ) *
      (((1 + ‖(2 * Real.pi) • ξ‖^2)⁻¹ : ℝ) * S ξ j))) :
    𝓕⁻ (outputFrequency A Z C μ x i S) x =
      (μ x : ℂ) * ((∑ a, ∑ j, (A x a i j : ℂ) * C x *
        𝓕⁻ (fun ξ ↦ Complex.I * (((2 * Real.pi) • ξ) a : ℝ) *
          (((1 + ‖(2 * Real.pi) • ξ‖^2)⁻¹ : ℝ) * S ξ j)) x) +
        ∑ j, (sourceProductCoefficient A Z C x i j : ℂ) *
          𝓕⁻ (fun ξ ↦ ((1 + ‖(2 * Real.pi) • ξ‖^2)⁻¹ : ℝ) * S ξ j) x) := by
  unfold outputFrequency
  rw [fourierInv_const_mul, fourierInv_add_integrable _ _
    (integrable_finsetSum _ (fun a _ ↦ integrable_finsetSum _ (fun j _ ↦ (hD a j).const_mul _)))
    (integrable_finsetSum _ (fun j _ ↦ (hS j).const_mul _))]
  rw [fourierInv_sum_integrable _ (fun a ↦ integrable_finsetSum _ (fun j _ ↦ (hD a j).const_mul _)),
    fourierInv_sum_integrable _ (fun j ↦ (hS j).const_mul _)]
  simp_rw [fourierInv_sum_integrable _ (fun j ↦ (hD _ j).const_mul _), fourierInv_const_mul]

private def entrySource (A : E → Fin d → Mat) (Z : E → Mat)
    (v : E → Fin d → ℂ) (l j : Fin d) (ξ : E) : ℂ :=
  𝓕 (fun y ↦ (-Complex.I * differentialPencil A y ((2 * Real.pi) • ξ) l j +
    Z y l j) * v y l) ξ

private theorem entrySource_eq_adjoint (A : E → Fin d → Mat) (Z : E → Mat)
    (v : E → Fin d → ℂ) (l : Fin d) :
    (fun ξ j ↦ entrySource A Z v l j ξ) =
      differentialAdjointSourceTransform (fun y a (_ : Unit) j ↦ A y a l j)
        (fun y (_ : Unit) j ↦ Z y l j) (fun y (_ : Unit) ↦ v y l) := by
  funext ξ j
  simp [entrySource, differentialAdjointSourceTransform, differentialPencil]

private theorem integrable_entry_input (A : E → Fin d → Mat) (Z : E → Mat)
    (v : E → Fin d → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun y ↦ A y a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun y ↦ Z y i j))
    (hv : ∀ i, ContDiff ℝ ∞ (fun y ↦ v y i))
    (hc : ∀ i, HasCompactSupport (fun y ↦ v y i)) (l j : Fin d) (ξ : E) :
    Integrable (fun y ↦ (-Complex.I * differentialPencil A y ((2 * Real.pi) • ξ) l j +
      Z y l j) * v y l) := by
  apply Continuous.integrable_of_hasCompactSupport _ (hc l).mul_left
  have ha a := (hA a l j).continuous
  have hz := (hZ l j).continuous
  have hv' := (hv l).continuous
  unfold differentialPencil
  fun_prop

private theorem adjointSource_eq_sum_entry (A : E → Fin d → Mat) (Z : E → Mat)
    (v : E → Fin d → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun y ↦ A y a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun y ↦ Z y i j))
    (hv : ∀ i, ContDiff ℝ ∞ (fun y ↦ v y i))
    (hc : ∀ i, HasCompactSupport (fun y ↦ v y i)) (ξ : E) (j : Fin d) :
    differentialAdjointSourceTransform A Z v ξ j = ∑ l, entrySource A Z v l j ξ := by
  exact fourier_sum_integrable _ (fun l ↦ integrable_entry_input A Z v hA hZ hv hc l j ξ) ξ

private theorem outputFrequency_eq_pencil (A : E → Fin d → Mat) (Z : E → Mat)
    (C μ : E → ℝ) (x : E) (i : Fin d) (S : E → Fin d → ℂ) (ξ : E) :
    outputFrequency A Z C μ x i S ξ =
      ∑ j, ((μ x : ℂ) * ((1 + ‖(2 * Real.pi) • ξ‖^2)⁻¹ : ℝ) *
        (Complex.I * C x * differentialPencil A x ((2 * Real.pi) • ξ) i j +
          sourceProductCoefficient A Z C x i j)) * S ξ j := by
  simp only [outputFrequency, differentialPencil, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a j ↦ _)]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _
  · apply Finset.sum_congr rfl
    intro a _
    ring
  · ring

private theorem sourceFull_eq_outputFrequency (A : E → Fin d → Mat) (Z : E → Mat)
    (C μ : E → ℝ) (v : E → Fin d → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun y ↦ A y a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun y ↦ Z y i j))
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hv : ∀ i, ContDiff ℝ ∞ (fun y ↦ v y i)) (x ξ : E) (i l : Fin d) :
    sourceAmplitudeTransform (fun x y ξ ↦ differentialFullAmplitude A Z C μ x y ξ i l)
      (fun y ↦ v y l) x ξ =
      outputFrequency A Z C μ x i
        (fun ξ j ↦ entrySource A Z (fun y l ↦ (μ y : ℂ) * v y l) l j ξ) ξ := by
  let w := fun y l ↦ (μ y : ℂ) * v y l
  have hw l : ContDiff ℝ ∞ (fun y ↦ w y l) :=
    (Complex.ofRealCLM.contDiff.comp hμ).mul (hv l)
  have hwc l : HasCompactSupport (fun y ↦ w y l) :=
    (hμc.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)).mul_right
  let L := fun j ↦ (μ x : ℂ) * ((1 + ‖(2 * Real.pi) • ξ‖^2)⁻¹ : ℝ) *
    (Complex.I * C x * differentialPencil A x ((2 * Real.pi) • ξ) i j +
      sourceProductCoefficient A Z C x i j)
  have he (y : E) : v y l * differentialFullAmplitude A Z C μ x y ξ i l =
      ∑ j, L j * ((-Complex.I * differentialPencil A y ((2 * Real.pi) • ξ) l j +
        Z y l j) * w y l) := by
    simp only [differentialFullAmplitude, imageBesselSymbol_sq, Complex.ofReal_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [L, w]
    ring
  rw [sourceAmplitudeTransform]
  simp only [smul_eq_mul, he]
  rw [fourier_sum_integrable _ (fun j ↦
    (integrable_entry_input A Z w hA hZ hw hwc l j ξ).const_mul (L j))]
  simp_rw [fourier_const_mul]
  exact (outputFrequency_eq_pencil A Z C μ x i (fun ξ j ↦ entrySource A Z w l j ξ) ξ).symm

private theorem integrable_entry_bessel (A : E → Fin d → Mat) (Z : E → Mat)
    (v : E → Fin d → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun y ↦ A y a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun y ↦ Z y i j))
    (hv : ∀ i, ContDiff ℝ ∞ (fun y ↦ v y i))
    (hc : ∀ i, HasCompactSupport (fun y ↦ v y i)) (l j : Fin d) :
    Integrable (fun ξ ↦ ((1 + ‖(2 * Real.pi) • ξ‖^2)⁻¹ : ℝ) * entrySource A Z v l j ξ) ∧
    ∀ a, Integrable (fun ξ ↦ Complex.I * (((2 * Real.pi) • ξ) a : ℝ) *
      (((1 + ‖(2 * Real.pi) • ξ‖^2)⁻¹ : ℝ) * entrySource A Z v l j ξ)) := by
  have he ξ j := congrFun (congrFun (entrySource_eq_adjoint A Z v l) ξ) j
  simp_rw [he]
  exact ⟨integrable_imageBesselSquared_adjointSourceTransform _ _ _
      (fun a _ j ↦ hA a l j) (fun _ j ↦ hZ l j) (fun _ ↦ hv l) (fun _ ↦ hc l) j,
    fun a ↦ integrable_frequency_derivative _ _ _
      (fun a _ j ↦ hA a l j) (fun _ j ↦ hZ l j) (fun _ ↦ hv l) (fun _ ↦ hc l) j a⟩

/-- Absolute frequency convergence of every source-tested matrix entry of
the full image amplitude. Smooth input need not be compact: the literal
measurement mask supplies the support (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integrable_sourceAmplitudeTransform_differentialFullAmplitude
    (A : E → Fin d → Mat) (Z : E → Mat) (C μ : E → ℝ) (v : E → Fin d → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun y ↦ A y a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun y ↦ Z y i j))
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hv : ∀ i, ContDiff ℝ ∞ (fun y ↦ v y i)) (x : E) (i l : Fin d) :
    Integrable (sourceAmplitudeTransform
      (fun x y ξ ↦ differentialFullAmplitude A Z C μ x y ξ i l) (fun y ↦ v y l) x) := by
  have he := funext (fun ξ ↦ sourceFull_eq_outputFrequency A Z C μ v hA hZ hμ hμc hv x ξ i l)
  rw [he]
  have hb := integrable_entry_bessel A Z (fun y l ↦ (μ y : ℂ) * v y l) hA hZ
    (fun l ↦ (Complex.ofRealCLM.contDiff.comp hμ).mul (hv l))
    (fun _ ↦ (hμc.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)).mul_right) l
  exact integrable_outputFrequency A Z C μ x i _ (fun j ↦ (hb j).1) (fun a j ↦ (hb j).2 a)

/-- The literal unregularized composite `μ P χ² J² P* μ` is the actual
source-first matrix full-amplitude operator, with the two opposite Fourier
phase factors and every cutoff retained. Convergence and the formal adjoint
identity are proved from smooth coefficients and the compact measurement
mask (`app:ch_background:prop:bg-frame`, Step 1, image-normal paragraph). -/
theorem coefficientImageNormal_eq_fullAmplitude
    (A : E → Fin d → Mat) (Z : E → Mat) (χ μ : E → ℝ) (v : E → Fin d → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun y ↦ A y a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun y ↦ Z y i j))
    (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hv : ∀ i, ContDiff ℝ ∞ (fun y ↦ v y i)) (x : E) (i : Fin d) :
    coefficientImageNormal A Z χ μ v hA hZ hμ hμc hv x i =
      matrixFullAmplitudeOperator (differentialFullAmplitude A Z (fun y ↦ χ y^2) μ) v x i := by
  let w := fun y l ↦ (μ y : ℂ) * v y l
  have hw l : ContDiff ℝ ∞ (fun y ↦ w y l) :=
    (Complex.ofRealCLM.contDiff.comp hμ).mul (hv l)
  have hwc l : HasCompactSupport (fun y ↦ w y l) :=
    (hμc.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)).mul_right
  have hsum (ξ : E) :
      (∑ l, sourceAmplitudeTransform
        (fun x y ξ ↦ differentialFullAmplitude A Z (fun y ↦ χ y^2) μ x y ξ i l)
          (fun y ↦ v y l) x ξ) =
      outputFrequency A Z (fun y ↦ χ y^2) μ x i (differentialAdjointSourceTransform A Z w) ξ := by
    simp_rw [sourceFull_eq_outputFrequency A Z _ μ v hA hZ hμ hμc hv,
      outputFrequency_eq_pencil]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, adjointSource_eq_sum_entry A Z w hA hZ hw hwc]
  rw [coefficientImageNormal_eq_frequency_factors A Z χ μ v hA hZ hχ hμ hμc hv]
  simp only [matrixFullAmplitudeOperator, fullAmplitudeOperator]
  rw [← fourierInv_sum_integrable _
    (fun l ↦ integrable_sourceAmplitudeTransform_differentialFullAmplitude A Z _ μ v
      hA hZ hμ hμc hv x i l)]
  have hfun : (fun ξ ↦ ∑ l, sourceAmplitudeTransform
        (fun x y ξ ↦ differentialFullAmplitude A Z (fun y ↦ χ y^2) μ x y ξ i l)
          (fun y ↦ v y l) x ξ) =
      outputFrequency A Z (fun y ↦ χ y^2) μ x i (differentialAdjointSourceTransform A Z w) :=
    funext hsum
  rw [hfun]
  have hInv := fourierInv_outputFrequency A Z (fun y ↦ χ y^2) μ x i
      (differentialAdjointSourceTransform A Z w)
      (fun j ↦ integrable_imageBesselSquared_adjointSourceTransform A Z w hA hZ hw hwc j)
      (fun a j ↦ integrable_frequency_derivative A Z w hA hZ hw hwc j a)
  simp only [Complex.ofReal_pow] at hInv
  exact hInv.symm

/-- Exact leading/remainder amplitude of the actual composite, for the
parent image-normal diagonal reduction (`app:ch_background:prop:bg-frame`,
Step 1). The remainder here is the explicit coefficient expression whose
physical derivatives are bounded in `PrimitiveBounds`. -/
theorem coefficientImageNormal_eq_leading_add_remainder
    (A : E → Fin d → Mat) (Z : E → Mat) (χ μ : E → ℝ) (v : E → Fin d → ℂ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun y ↦ A y a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun y ↦ Z y i j))
    (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hv : ∀ i, ContDiff ℝ ∞ (fun y ↦ v y i)) (x : E) (i : Fin d) :
    coefficientImageNormal A Z χ μ v hA hZ hμ hμc hv x i =
      matrixFullAmplitudeOperator (fun x y ξ ↦
        differentialLeadingAmplitude A (fun z ↦ χ z^2) μ x y ξ +
        differentialRemainderAmplitude A Z (fun z ↦ χ z^2) μ x y ξ) v x i := by
  rw [coefficientImageNormal_eq_fullAmplitude A Z χ μ v hA hZ hχ hμ hμc hv]
  apply congrArg (fun c : E → E → E → Matrix (Fin d) (Fin d) ℂ ↦
    matrixFullAmplitudeOperator c v x i)
  funext x y ξ
  exact differentialFullAmplitude_eq_leading_add_remainder A Z (fun z ↦ χ z^2) μ x y ξ

end JanetCartan.ContinuumNormalReduction.ImageNormal
