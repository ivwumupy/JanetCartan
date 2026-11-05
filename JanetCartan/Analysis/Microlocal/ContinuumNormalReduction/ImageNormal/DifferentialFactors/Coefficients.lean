module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Reduced.Formula
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Phase

/-!
# The differential factors of the Euclidean image normal

The coefficient expansion used in `app:ch_background:prop:bg-frame`, Step 1.
The zeroth coefficient is retained, and the geometric specialization is the
actual reduced strain operator, including its connection term.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped RealInnerProductSpace
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Real principal pencil of `P = ∑ Aᵃ ∂ₐ + Z`, for the image-normal
paragraph of `app:ch_background:prop:bg-frame`. Its argument is a physical covector. -/
def differentialPencil (A : E → Fin d → Matrix I J ℝ) (x k : E) : Matrix I J ℝ :=
  fun i j ↦ ∑ a, A x a i j * k a

/-- Literal complexification of the real differential operator in
`app:ch_background:prop:bg-frame`, Step 1. -/
def coefficientOperator (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (u : E → J → ℂ) (x : E) (i : I) : ℂ :=
  (∑ a, ∑ j, (A x a i j : ℂ) * partialDeriv (fun z ↦ u z j) x a) +
    ∑ j, (Z x i j : ℂ) * u x j

/-- The literal divergence-form formal adjoint, before integration by parts,
in `app:ch_background:prop:bg-frame`, Step 1. The real coefficient matrices
are transposed; the derivative acts on their product with the test field. -/
def coefficientFormalAdjoint (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (v : E → I → ℂ) (y : E) (j : J) : ℂ :=
  -(∑ a, ∑ i, partialDeriv (fun z ↦ (A z a i j : ℂ) * v z i) y a) +
    ∑ i, (Z y i j : ℂ) * v y i

/-- The entire new zeroth coefficient after source multiplication, namely
`Q = ∑ Aᵃ ∂ₐC + ZC` (`app:ch_background:prop:bg-frame`, Step 1). -/
def sourceProductCoefficient (A : E → Fin d → Matrix I J ℝ)
    (Z : E → Matrix I J ℝ) (C : E → ℝ) (x : E) : Matrix I J ℝ :=
  fun i j ↦ (∑ a, A x a i j * partialDeriv C x a) + Z x i j * C x

/-- Geometric specialization of the principal pencil is the manuscript's
`M_G`, with the original symmetry hypothesis (`app:ch_waves:eq:reduced-symbol`). -/
theorem differentialPencil_geometric (Q : E → Fin d → MetricTensor d)
    (x k : E) (hQ : ∀ i, (Q x i).IsSymm) :
    differentialPencil (fun z ↦ NullTransport.principalCoefficient (Q z)) x k =
      NullTransport.reducedSymbol (Q x) k := by
  rw [NullTransport.reducedSymbol_eq_sum _ hQ]
  ext i j
  simp only [differentialPencil, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [mul_comm]

/-- The coefficient operator really is `P_G`, including the induced
connection (`app:ch_waves:eq:reduced-symbol`). -/
theorem coefficientOperator_geometric {N : ℕ} (G : E → Euclidean N)
    (Q : E → Fin d → MetricTensor d) (u : E → E) (x : E)
    (hQ : ∀ i, (Q x i).IsSymm) (i : Fin d) :
    coefficientOperator (fun z ↦ NullTransport.principalCoefficient (Q z))
      (fun z ↦ GeometricProfile.reducedZerothCoefficient G (Q z) z)
      (fun z j ↦ (u z j : ℂ)) x i = (NullTransport.reducedOperator G Q u x i : ℂ) := by
  rw [GeometricProfile.reducedOperator_eq_coefficients G Q u x hQ i]
  simp only [coefficientOperator, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  by_cases hu : DifferentiableAt ℝ (fun z ↦ u z j) x
  · exact congrArg (fun L : E →L[ℝ] ℂ ↦ L (EuclideanSpace.single a 1))
      (Complex.ofRealCLM.hasFDerivAt.comp x hu.hasFDerivAt).fderiv
  · have hc : ¬ DifferentiableAt ℝ (fun z ↦ (u z j : ℂ)) x := by
      intro hc
      exact hu (by simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using Complex.reCLM.differentiableAt.comp x hc)
    simp [partialDeriv, fderiv_zero_of_not_differentiableAt hu,
      fderiv_zero_of_not_differentiableAt hc]

omit [Fintype I] [Fintype J] in
/-- Differentiating the actual source square gives the factor two; no
cutoff derivative is omitted (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem sourceProductCoefficient_square (A : E → Fin d → Matrix I J ℝ)
    (Z : E → Matrix I J ℝ) (χ : E → ℝ) (x : E)
    (hχ : DifferentiableAt ℝ χ x) (i : I) (j : J) :
    sourceProductCoefficient A Z (fun z ↦ χ z ^ 2) x i j =
      (∑ a, A x a i j * (2 * χ x * partialDeriv χ x a)) + Z x i j * χ x ^ 2 := by
  simp only [sourceProductCoefficient, partialDeriv, (hχ.hasFDerivAt.pow 2).fderiv]
  simp

end JanetCartan.ContinuumNormalReduction.ImageNormal
