module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.DifferentialFactors.Coefficients
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.BesselSymbol
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition

/-!
# Explicit coefficient expansion of the image amplitude

For `app:ch_background:prop:bg-frame`, Step 1, expand the two differential
factors around `C J²`, retaining `Q = ∑ Aᵃ ∂ₐC + ZC`. The leading term has
positive sign because the output and integrated source phase factors are
`i M(x,k)` and `-i M(y,k)ᵀ`. Operator identification is a separate obligation
from this pointwise algebraic expansion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped RealInnerProductSpace
open JanetCartan.Pseudodifferential
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Mat" => Matrix (Fin d) (Fin d) ℝ

/-- Full differential-factor amplitude around `C J²`, with both measurement
masks (`app:ch_background:prop:bg-frame`, Step 1). -/
def differentialFullAmplitude (A : E → Fin d → Mat) (Z : E → Mat)
    (C μ : E → ℝ) (x y ξ : E) : Matrix (Fin d) (Fin d) ℂ :=
  fun i l ↦ (μ x * μ y : ℝ) * (imageBesselSymbol ξ * imageBesselSymbol ξ : ℝ) *
    ∑ j, (Complex.I * C x * differentialPencil A x ((2 * Real.pi) • ξ) i j +
        sourceProductCoefficient A Z C x i j) *
      (-Complex.I * differentialPencil A y ((2 * Real.pi) • ξ) l j + Z y l j)

/-- Leading full amplitude, before diagonal reduction
(`app:ch_background:prop:bg-frame`, Step 1). -/
def differentialLeadingAmplitude (A : E → Fin d → Mat) (C μ : E → ℝ)
    (x y ξ : E) : Matrix (Fin d) (Fin d) ℂ :=
  fun i l ↦ (μ x * μ y * C x * (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ : ℝ) *
    ((differentialPencil A x ((2 * Real.pi) • ξ) *
      (differentialPencil A y ((2 * Real.pi) • ξ)).transpose) i l : ℝ)

/-- Every zeroth-order and differentiated source-cutoff term, explicitly
constructed for `app:ch_background:prop:bg-frame`, Step 1. -/
def differentialRemainderAmplitude (A : E → Fin d → Mat) (Z : E → Mat)
    (C μ : E → ℝ) (x y ξ : E) : Matrix (Fin d) (Fin d) ℂ :=
  fun i l ↦ (μ x * μ y * (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ : ℝ) *
    ∑ j, (Complex.I * C x * differentialPencil A x ((2 * Real.pi) • ξ) i j * Z y l j -
      Complex.I * sourceProductCoefficient A Z C x i j *
        differentialPencil A y ((2 * Real.pi) • ξ) l j +
      (sourceProductCoefficient A Z C x i j : ℂ) * Z y l j)

/-- Exact expansion of the full amplitude, with the positive `MMᵀ` leading
term and all lower-order coefficients (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem differentialFullAmplitude_eq_leading_add_remainder
    (A : E → Fin d → Mat) (Z : E → Mat) (C μ : E → ℝ) (x y ξ : E) :
    differentialFullAmplitude A Z C μ x y ξ =
      differentialLeadingAmplitude A C μ x y ξ +
        differentialRemainderAmplitude A Z C μ x y ξ := by
  ext i l
  simp only [differentialFullAmplitude, differentialLeadingAmplitude,
    differentialRemainderAmplitude, imageBesselSymbol_sq, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Complex.ofReal_mul, Complex.ofReal_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  linear_combination
    -(μ x : ℂ) * μ y * ((1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ : ℝ) * C x *
      differentialPencil A x ((2 * Real.pi) • ξ) i j *
      differentialPencil A y ((2 * Real.pi) • ξ) l j * Complex.I_sq

/-- The geometric leading piece is precisely the manuscript's two-position
symbol product at physical covector `2πξ`, with every fixed cutoff
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem differentialLeadingAmplitude_geometric
    (Q : E → Fin d → MetricTensor d) (χ μ : E → ℝ) (x y ξ : E)
    (hx : ∀ i, (Q x i).IsSymm) (hy : ∀ i, (Q y i).IsSymm) :
    differentialLeadingAmplitude (fun z ↦ NullTransport.principalCoefficient (Q z))
      (fun z ↦ χ z ^ 2) μ x y ξ =
    fun i l ↦ ((μ x * μ y * χ x ^ 2 * (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) *
      ((NullTransport.reducedSymbol (Q x) ((2 * Real.pi) • ξ) *
        (NullTransport.reducedSymbol (Q y) ((2 * Real.pi) • ξ)).transpose) i l : ℝ) := by
  unfold differentialLeadingAmplitude
  rw [differentialPencil_geometric Q x _ hx, differentialPencil_geometric Q y _ hy]

/-- Actual output phase differentiation supplies the factor `+i kₐ`,
including the derivative of `C` (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem partialDeriv_source_phase (C : E → ℝ) (x y ξ : E)
    (hC : DifferentiableAt ℝ C x) (a : Fin d) :
    partialDeriv (fun z ↦ (Real.fourierChar ⟪ξ, z - y⟫ : ℂ) * C z) x a =
      (Real.fourierChar ⟪ξ, x - y⟫ : ℂ) *
        (((partialDeriv C x a : ℝ) : ℂ) + Complex.I * (((2 * Real.pi) • ξ) a : ℝ) * C x) := by
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hC.hasFDerivAt
  change HasFDerivAt (fun z ↦ (C z : ℂ)) _ x at hc
  unfold partialDeriv
  rw [fderiv_fourierChar_mul (fun z ↦ (C z : ℂ)) x y ξ
    (EuclideanSpace.single a 1) hc.differentiableAt, hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul, PiLp.smul_apply,
    smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- Applying the literal coefficient operator to the source-masked plane
wave gives exactly the output factor of `differentialFullAmplitude`
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientOperator_source_phase (A : E → Fin d → Mat) (Z : E → Mat)
    (C : E → ℝ) (x y ξ : E) (hC : DifferentiableAt ℝ C x)
    (w : Fin d → ℂ) (i : Fin d) :
    coefficientOperator A Z
      (fun z j ↦ ((Real.fourierChar ⟪ξ, z - y⟫ : ℂ) * C z) * w j) x i =
      (Real.fourierChar ⟪ξ, x - y⟫ : ℂ) *
        ∑ j, (Complex.I * C x * differentialPencil A x ((2 * Real.pi) • ξ) i j +
          sourceProductCoefficient A Z C x i j) * w j := by
  have hp : DifferentiableAt ℝ (fun z ↦ (Real.fourierChar ⟪ξ, z - y⟫ : ℂ) * C z) x :=
    ((contDiff_fourierChar.comp ((innerSL ℝ ξ).contDiff.comp
      (contDiff_id.sub contDiff_const))).differentiable (by simp) x).mul
        (Complex.ofRealCLM.differentiableAt.comp x hC)
  have hd (a j : Fin d) :
      partialDeriv (fun z ↦ ((Real.fourierChar ⟪ξ, z - y⟫ : ℂ) * C z) * w j) x a =
        ((Real.fourierChar ⟪ξ, x - y⟫ : ℂ) *
          (((partialDeriv C x a : ℝ) : ℂ) +
            Complex.I * (((2 * Real.pi) • ξ) a : ℝ) * C x)) * w j := by
    rw [partialDeriv, (hp.hasFDerivAt.mul_const (w j)).fderiv]
    rw [smul_apply, smul_eq_mul, mul_comm (w j)]
    change partialDeriv (fun z ↦ (Real.fourierChar ⟪ξ, z - y⟫ : ℂ) * C z) x a * w j = _
    rw [partialDeriv_source_phase C x y ξ hC a]
  simp only [coefficientOperator, hd, differentialPencil, sourceProductCoefficient,
    Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.mul_sum, Finset.sum_mul, add_mul]
  rw [Finset.sum_comm (f := fun a j ↦ _)]
  simp only [← Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    ring
  · ring

end JanetCartan.ContinuumNormalReduction.ImageNormal
