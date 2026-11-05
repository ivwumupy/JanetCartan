module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CompactNormal
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Bridges

/-!
# The compact graph on vector-valued Lebesgue L²

The compact graphs of `NormalKernel` are transported by the existing finite
coordinate isometry. Their actual adjoints and the exact cycle-frequency
cross normal are retained (`app:ch_regular_base:eq:actual-normal-kernel`).
This is the vector graph consumed by the low-bound construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.LowBounds

open NormalComparison NormalKernel Pseudodifferential

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

variable {S : Euclidean n → Euclidean n → ℝ}
variable {A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}

/-- The constructed compact graph on the same finite-fiber Euclidean L² as
`L2Realization`, using its already proved isometric coordinate bridge.
Source: `app:ch_regular_base:eq:actual-normal-kernel`. -/
def compactVectorGraph (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : E × E ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : E × E ↦ A p.1 p.2 i k)) : H →L[ℂ] H :=
  by exact vectorMatrixL2Operator (graphBlock hS hA hsA)

/-- Coordinate transfer is exact, with no measure or norm-equivalence factor
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem coordinates_compactVectorGraph (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : E × E ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : E × E ↦ A p.1 p.2 i k)) (f : H) :
    finiteL2CoordinateIsometry volume (compactVectorGraph hS hA hsA f) =
      compactGraph hS hA hsA (finiteL2CoordinateIsometry volume f) := by
  rw [compactVectorGraph, finiteL2CoordinateIsometry_vectorMatrixL2Operator,
    matrixOperator_eq_normalKernel_blocks]
  rfl

/-- The actual Hilbert adjoint commutes with the coordinate transfer, for
`app:ch_regular_base:eq:actual-normal-kernel`. -/
theorem coordinates_compactVectorGraph_adjoint (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : E × E ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : E × E ↦ A p.1 p.2 i k)) (f : H) :
    finiteL2CoordinateIsometry volume ((compactVectorGraph hS hA hsA).adjoint f) =
      (compactGraph hS hA hsA).adjoint (finiteL2CoordinateIsometry volume f) := by
  rw [compactVectorGraph, vectorMatrixL2Operator_adjoint,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator,
    matrixOperator_eq_normalKernel_blocks, compactGraph, blocks_adjoint]

/-- The constructed vector graph equals the literal iterated graph integral
on L¹ ∩ L², in physical covectors with factor `(2π)⁻ⁿ`.
Source: `app:ch_regular_base:eq:actual-normal-kernel`. -/
theorem compactVectorGraph_ae_graphOperator (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : E × E ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : E × E ↦ A p.1 p.2 i k))
    (f : H) (hf : ∀ k, Integrable (fun y ↦ f y k)) :
    compactVectorGraph hS hA hsA f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun x _ η ↦ A x η) (fun y k ↦ f y k) x) := by
  have hc := ae_all_iff.mpr (fun k ↦ finiteL2Coordinates_apply_ae volume f k)
  have hi (k) : Integrable ((finiteL2CoordinateIsometry volume f) k : E → ℂ) :=
    (hf k).congr (finiteL2Coordinates_apply_ae volume f k).symm
  have he (x : E) : graphOperator S (fun x _ η ↦ A x η)
      (fun y k ↦ (finiteL2CoordinateIsometry volume f) k y) x =
      graphOperator S (fun x _ η ↦ A x η) (fun y k ↦ f y k) x := by
    unfold graphOperator
    congr 1
    apply integral_congr_ae
    filter_upwards [] with η
    apply integral_congr_ae
    filter_upwards [hc] with y hy
    congr 2
    exact funext hy
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro i
  rw [coordinates_compactVectorGraph]
  simpa only [he, PiLp.toLp_apply] using
    compactGraph_ae_graphOperator hS hA hsA (finiteL2CoordinateIsometry volume f) hi i

/-- The vector Hilbert adjoint is the literal reverse integral on every L²
input, with the same physical normalization. This makes no identification with
the manuscript's weighted inverse (`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem compactVectorGraph_adjoint_ae_reverseIntegral
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : E × E ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : E × E ↦ A p.1 p.2 i k)) (f : H) :
    (compactVectorGraph hS hA hsA).adjoint f =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ x,
        star (graphOscillation S x y η) • (A x η).conjTranspose.mulVec (fun i ↦ f x i)) := by
  have hc := ae_all_iff.mpr (fun i ↦ finiteL2Coordinates_apply_ae volume f i)
  have he (y : E) :
      (∫ η, ∫ x, star (graphOscillation S x y η) •
        (A x η).conjTranspose.mulVec (fun i ↦ (finiteL2CoordinateIsometry volume f) i x)) =
      ∫ η, ∫ x, star (graphOscillation S x y η) •
        (A x η).conjTranspose.mulVec (fun i ↦ f x i) := by
    apply integral_congr_ae
    filter_upwards [] with η
    apply integral_congr_ae
    filter_upwards [hc] with x hx
    congr 2
    exact funext hx
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro k
  rw [coordinates_compactVectorGraph_adjoint]
  simpa only [he, PiLp.toLp_apply] using
    compactGraph_adjoint_ae_reverseIntegral hS hA hsA (finiteL2CoordinateIsometry volume f) k

/-- Literal vector cross normal on every Euclidean L² input, with both physical
output positions, the full amplitude product, and the inverse Jacobian. The
normal is computed from the constructed graphs; it is never an input field.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem compactVectorGraph_cross_ae_cycleIntegral
    {K D : Set E} {η : E → E → E → E}
    {J : E → E → E → E →L[ℝ] E} {δ : ℝ}
    (G : AveragedGradientChart S K D η J δ)
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : E × E ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : E × E ↦ A p.1 p.2 i k))
    (hB : ∀ j k, Continuous (fun p : E × E ↦ B p.1 p.2 j k))
    (hsB : ∀ j k, HasCompactSupport (fun p : E × E ↦ B p.1 p.2 j k))
    (hcarrierA : ∀ x u, x ∉ K ∨ u ∉ D → A x u = 0)
    (hcarrierB : ∀ y u, y ∉ K → B y u = 0)
    (f : H) :
    compactVectorGraph hS hA hsA ((compactVectorGraph hS hB hsB).adjoint f) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ ∑ j, ∫ y, (∫ ξ,
        Complex.exp ((2 * Real.pi * inner ℝ (x - y) ξ : ℝ) * Complex.I) *
          cycleCrossNormalAmplitude D S A B η J x y ξ i j) * f y j) := by
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro i
  rw [coordinates_compactVectorGraph, coordinates_compactVectorGraph_adjoint]
  refine (compactGraph_cross_ae_cycleIntegral G hS hA hsA hB hsB hcarrierA hcarrierB
    (finiteL2CoordinateIsometry volume f) i).trans ?_
  apply Filter.Eventually.of_forall
  intro x
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [finiteL2Coordinates_apply_ae volume f j] with y hy
  rw [show (finiteL2CoordinateIsometry volume f) j y = f y j from hy]

end JanetCartan.FourierIntegral.LowBounds
