module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.Scalar
public import Mathlib.Analysis.Matrix.Normed

/-!
# Finite matrix pseudodifferential operators

For `app:ch_regular_base:thm:actual-calculus`, finite coordinate sums of the
actual scalar integrals define operators on finite complex vector data. The
integral identifications below justify these sums as vector Bochner integrals.
Matrix amplitudes use the project's Frobenius norm and unit-frequency `2π` phase.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix.Norms.Frobenius
namespace JanetCartan.Pseudodifferential
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

/-- `app:ch_regular_base:thm:actual-calculus`: the full operator on finite
complex vector data; the input index is the column index of the amplitude. -/
def matrixFullAmplitudeOperator (c : V → V → V → Matrix I J ℂ)
    (u : V → J → ℂ) (x : V) : I → ℂ :=
  fun i ↦ ∑ j, fullAmplitudeOperator (fun x y ξ ↦ c x y ξ i j) (fun y ↦ u y j) x

/-- `app:ch_regular_base:thm:actual-calculus`: source-independent matrix action
on a finite family of scalar Schwartz functions (the coordinates of vector data). -/
def matrixSourceIndependentOperator (b : V → V → Matrix I J ℂ)
    (u : J → 𝓢(V, ℂ)) (x : V) : I → ℂ :=
  fun i ↦ ∑ j, sourceIndependentOperator (fun x η ↦ b x η i j) (u j) x

/-- `app:ch_regular_base:thm:actual-calculus`: the matrix composite symbol,
with the ordered contraction `cᵢⱼ bⱼₖ` over the intermediate vector index. -/
def matrixComposedSymbol (c : V → V → V → Matrix I J ℂ)
    (b : V → V → Matrix J K ℂ) (x η : V) : Matrix I K ℂ :=
  fun i k ↦ ∑ j, composedSymbol (fun x y ξ ↦ c x y ξ i j) (fun y η ↦ b y η j k) x η

/-- `app:ch_regular_base:thm:actual-calculus`: the matrix source-independent
operator is the actual vector-valued inverse Fourier integral. -/
theorem matrixSourceIndependentOperator_eq_integral
    (b : V → V → Matrix I J ℂ) (u : J → 𝓢(V, ℂ)) (x : V)
    (h : ∀ i j, Integrable (fun η ↦ (𝓕 (u j) : 𝓢(V, ℂ)) η * b x η i j)) :
    matrixSourceIndependentOperator b u x =
      ∫ η, Real.fourierChar ⟪η, x⟫ • (b x η).mulVec (fun j ↦ (𝓕 (u j) : 𝓢(V, ℂ)) η) := by
  have hp (i j) : Integrable (fun η ↦ Real.fourierChar ⟪η, x⟫ •
      ((𝓕 (u j) : 𝓢(V, ℂ)) η * b x η i j)) := by
    simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (-x)).2 (h i j)
  have heq (η : V) (i : I) :
      (Real.fourierChar ⟪η, x⟫ • (b x η).mulVec (fun j ↦ (𝓕 (u j) : 𝓢(V, ℂ)) η)) i =
      ∑ j, Real.fourierChar ⟪η, x⟫ • ((𝓕 (u j) : 𝓢(V, ℂ)) η * b x η i j) := by
    change Real.fourierChar ⟪η, x⟫ • (∑ j, b x η i j * (𝓕 (u j) : 𝓢(V, ℂ)) η) = _
    simp only [Finset.smul_sum, mul_comm]
  funext i
  rw [eval_integral (fun i ↦ by simp_rw [heq]; exact integrable_finsetSum _ (fun j _ ↦ hp i j))]
  simp_rw [heq]
  rw [integral_finsetSum _ (fun j _ ↦ hp i j)]
  simp only [matrixSourceIndependentOperator, sourceIndependentOperator, Real.fourierInv_eq, smul_eq_mul]

/-- `app:ch_regular_base:thm:actual-calculus`: the full matrix operator is the
actual source-first vector Bochner integral, with the `2π` Fourier convention. -/
theorem matrixFullAmplitudeOperator_eq_integral
    (c : V → V → V → Matrix I J ℂ) (u : V → J → ℂ) (x : V)
    (hy : ∀ i j ξ, Integrable (fun y ↦ u y j * c x y ξ i j))
    (hξ : ∀ i j, Integrable (sourceAmplitudeTransform (fun x y ξ ↦ c x y ξ i j)
      (fun y ↦ u y j) x)) :
    matrixFullAmplitudeOperator c u x =
      ∫ ξ, Real.fourierChar ⟪ξ, x⟫ •
        ∫ y, Real.fourierChar (-⟪y, ξ⟫) • (c x y ξ).mulVec (u y) := by
  have hsource (ξ : V) :
      (∫ y, Real.fourierChar (-⟪y, ξ⟫) • (c x y ξ).mulVec (u y)) =
        fun i ↦ ∑ j, sourceAmplitudeTransform (fun x y ξ ↦ c x y ξ i j) (fun y ↦ u y j) x ξ := by
    have hp (i j) := (Real.fourierIntegral_convergent_iff ξ).2 (hy i j ξ)
    have heq (y : V) (i : I) :
        (Real.fourierChar (-⟪y, ξ⟫) • (c x y ξ).mulVec (u y)) i =
        ∑ j, Real.fourierChar (-⟪y, ξ⟫) • (u y j * c x y ξ i j) := by
      change Real.fourierChar (-⟪y, ξ⟫) • (∑ j, c x y ξ i j * u y j) = _
      simp only [Finset.smul_sum, mul_comm]
    funext i
    rw [eval_integral (fun i ↦ by simp_rw [heq]; exact integrable_finsetSum _ (fun j _ ↦ hp i j))]
    simp_rw [heq]
    rw [integral_finsetSum _ (fun j _ ↦ hp i j)]
    rfl
  simp_rw [hsource]
  have hp (i j) : Integrable (fun ξ ↦ Real.fourierChar ⟪ξ, x⟫ •
      sourceAmplitudeTransform (fun x y ξ ↦ c x y ξ i j) (fun y ↦ u y j) x ξ) := by
    simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (-x)).2 (hξ i j)
  funext i
  have heval (ξ : V) (i : I) :
      (Real.fourierChar ⟪ξ, x⟫ • (fun i ↦ ∑ j, sourceAmplitudeTransform
        (fun x y ξ ↦ c x y ξ i j) (fun y ↦ u y j) x ξ)) i =
      ∑ j, Real.fourierChar ⟪ξ, x⟫ • sourceAmplitudeTransform
        (fun x y ξ ↦ c x y ξ i j) (fun y ↦ u y j) x ξ := by
    change Real.fourierChar ⟪ξ, x⟫ • (∑ j : J, sourceAmplitudeTransform
      (fun x y ξ ↦ c x y ξ i j) (fun y ↦ u y j) x ξ) = _
    rw [Finset.smul_sum]
  rw [eval_integral (fun i ↦ by
    simp_rw [heval]
    exact integrable_finsetSum _ (fun j _ ↦ hp i j))]
  simp_rw [heval]
  rw [integral_finsetSum _ (fun j _ ↦ hp i j)]
  simp only [matrixFullAmplitudeOperator, fullAmplitudeOperator, Real.fourierInv_eq, Circle.smul_def]
end JanetCartan.Pseudodifferential
