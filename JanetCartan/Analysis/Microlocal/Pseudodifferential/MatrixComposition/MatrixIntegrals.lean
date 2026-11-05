module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.Basic

/-!
# Bochner integrals of Frobenius matrices

Coordinate integration and the literal ordered matrix integral for the symbol
in `app:ch_regular_base:thm:actual-calculus`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix.Norms.Frobenius
namespace JanetCartan.Pseudodifferential
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

/-- `app:ch_regular_base:thm:actual-calculus`: continuous coordinates for the
Frobenius matrix space; no replacement of the matrix norm is made. -/
def matrixEntryEquiv : Matrix I J ℂ ≃L[ℂ] (I × J → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun A p ↦ A p.1 p.2
      invFun := fun f i j ↦ f (i, j)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- `app:ch_regular_base:thm:actual-calculus`: evaluation of an actual
Frobenius-matrix Bochner integral at an entry. -/
theorem matrix_integral_apply {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : X → Matrix I J ℂ) (hf : ∀ i j, Integrable (fun x ↦ f x i j) μ) (i : I) (j : J) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  let e := matrixEntryEquiv (I := I) (J := J)
  calc
    _ = (∫ x, e (f x) ∂μ) (i, j) :=
      congrArg (fun g : I × J → ℂ ↦ g (i, j)) (e.integral_comp_comm f).symm
    _ = _ := eval_integral (f := fun x p ↦ f x p.1 p.2) (fun p ↦ hf p.1 p.2) (i, j)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- `app:ch_regular_base:thm:actual-calculus`: the finite contraction defining
the composite symbol is the actual iterated matrix Bochner integral. Its
integrand contains the ordered matrix product `c x y ξ * b y η`. -/
theorem matrixComposedSymbol_eq_integral
    (c : V → V → V → Matrix I J ℂ) (b : V → V → Matrix J K ℂ) (x η : V)
    (hy : ∀ i j k ξ, Integrable (fun y ↦
      symbolPlaneWave (fun y η ↦ b y η j k) η y * c x y ξ i j))
    (hξ : ∀ i j k, Integrable (sourceAmplitudeTransform (fun x y ξ ↦ c x y ξ i j)
      (symbolPlaneWave (fun y η ↦ b y η j k) η) x)) :
    matrixComposedSymbol c b x η = Real.fourierChar (-⟪η, x⟫) •
      ∫ ξ, Real.fourierChar ⟪ξ, x⟫ •
        ∫ y, Real.fourierChar (-⟪y, ξ⟫) •
          (Real.fourierChar ⟪η, y⟫ • (c x y ξ * b y η)) := by
  have hsource (ξ : V) (i : I) (k : K) :
      (∫ y, Real.fourierChar (-⟪y, ξ⟫) •
        (Real.fourierChar ⟪η, y⟫ • (c x y ξ * b y η))) i k =
        ∑ j, sourceAmplitudeTransform (fun x y ξ ↦ c x y ξ i j)
          (symbolPlaneWave (fun y η ↦ b y η j k) η) x ξ := by
    have heq (y : V) (i : I) (k : K) :
        (Real.fourierChar (-⟪y, ξ⟫) • (Real.fourierChar ⟪η, y⟫ • (c x y ξ * b y η))) i k =
        ∑ j, Real.fourierChar (-⟪y, ξ⟫) •
          (symbolPlaneWave (fun y η ↦ b y η j k) η y * c x y ξ i j) := by
      simp only [Circle.smul_def, Matrix.smul_apply, Matrix.mul_apply,
        smul_eq_mul, symbolPlaneWave, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hp (i j k) := (Real.fourierIntegral_convergent_iff ξ).2 (hy i j k ξ)
    rw [matrix_integral_apply _ (fun i k ↦ by
      simp_rw [heq]
      exact integrable_finsetSum _ (fun j _ ↦ hp i j k))]
    simp_rw [heq]
    rw [integral_finsetSum _ (fun j _ ↦ hp i j k)]
    rfl
  have hp (i j k) : Integrable (fun ξ ↦ Real.fourierChar ⟪ξ, x⟫ •
      sourceAmplitudeTransform (fun x y ξ ↦ c x y ξ i j)
        (symbolPlaneWave (fun y η ↦ b y η j k) η) x ξ) := by
    simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (-x)).2 (hξ i j k)
  have heval (ξ : V) (i : I) (k : K) :
      (Real.fourierChar ⟪ξ, x⟫ • ∫ y, Real.fourierChar (-⟪y, ξ⟫) •
        (Real.fourierChar ⟪η, y⟫ • (c x y ξ * b y η))) i k =
      ∑ j, Real.fourierChar ⟪ξ, x⟫ • sourceAmplitudeTransform
        (fun x y ξ ↦ c x y ξ i j) (symbolPlaneWave (fun y η ↦ b y η j k) η) x ξ := by
    change Real.fourierChar ⟪ξ, x⟫ • ((∫ y, Real.fourierChar (-⟪y, ξ⟫) •
      (Real.fourierChar ⟪η, y⟫ • (c x y ξ * b y η))) i k) = _
    rw [hsource, Finset.smul_sum]
  ext i k
  change matrixComposedSymbol c b x η i k = Real.fourierChar (-⟪η, x⟫) •
    ((∫ ξ, Real.fourierChar ⟪ξ, x⟫ • ∫ y, Real.fourierChar (-⟪y, ξ⟫) •
      (Real.fourierChar ⟪η, y⟫ • (c x y ξ * b y η))) i k)
  rw [matrix_integral_apply _ (fun i k ↦ by
    simp_rw [heval]
    exact integrable_finsetSum _ (fun j _ ↦ hp i j k))]
  simp_rw [heval]
  rw [integral_finsetSum _ (fun j _ ↦ hp i j k)]
  simp only [matrixComposedSymbol, composedSymbol, fullAmplitudeOperator,
    Real.fourierInv_eq, Finset.smul_sum]
end JanetCartan.Pseudodifferential
