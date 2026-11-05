module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The induced metric and its linearization

Coordinate definitions used in Section 2 of paper.tex. The target dimension is the
Janet–Cartan dimension. Metric preservation is a condition on the differential.

The elementary metric identities in this file are proved using finite-dimensional
linear algebra and differential calculus.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan

/-- The universal target dimension in Theorem 1.1. -/
def embeddingDimension (n : ℕ) : ℕ := n * (n + 1) / 2

/-- The normal dimension of an immersion in the Janet–Cartan dimension. -/
def normalDimension (n : ℕ) : ℕ := n * (n - 1) / 2

/-- Euclidean coordinate space, with its Euclidean norm. -/
abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Coordinate arrays for covariant two-tensors. Symmetry is imposed when needed. -/
abbrev MetricTensor (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A tensor field on a coordinate domain. -/
abbrev MetricField (n : ℕ) := Euclidean n → MetricTensor n

/-- A smooth positive definite metric on an open coordinate domain. -/
def IsRiemannianMetricOn {n : ℕ} (g : MetricField n) (s : Set (Euclidean n)) : Prop :=
  ContDiffOn ℝ ∞ g s ∧ ∀ x ∈ s, (g x).PosDef

/-- A coordinate derivative. -/
def partialDeriv {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Euclidean n → E) (x : Euclidean n) (i : Fin n) : E :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The induced metric γ(F) = (dF)ᵀ dF. -/
def inducedMetric {n N : ℕ} (F : Euclidean n → Euclidean N) : MetricField n :=
  fun x i j ↦ inner ℝ (partialDeriv F x i) (partialDeriv F x j)

/-- The linearized metric Dγ_F Y, with the normalization in Section 2. -/
def linearizedMetric {n N : ℕ} (F Y : Euclidean n → Euclidean N) : MetricField n :=
  fun x i j ↦
    inner ℝ (partialDeriv F x i) (partialDeriv Y x j) +
      inner ℝ (partialDeriv Y x i) (partialDeriv F x j)

/-- An immersion on a coordinate domain, expressed using its differential. -/
def IsImmersionOn {n N : ℕ} (F : Euclidean n → Euclidean N)
    (s : Set (Euclidean n)) : Prop :=
  ∀ x ∈ s, Function.Injective (fderiv ℝ F x)

/-- The metric equation on a coordinate domain. -/
def IsIsometricOn {n N : ℕ} (g : MetricField n) (F : Euclidean n → Euclidean N)
    (s : Set (Euclidean n)) : Prop :=
  EqOn (inducedMetric F) g s

/-- Frobenius contraction of two coordinate tensors. -/
def tensorPairing {n : ℕ} (A B : MetricTensor n) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- The normal space of the differential at a point. -/
def normalSpace {n N : ℕ} (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    Submodule ℝ (Euclidean N) :=
  (LinearMap.range (fderiv ℝ F x).toLinearMap)ᗮ

/-- The second fundamental form, as an ambient-vector-valued coordinate tensor. -/
def secondFundamentalForm {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (i j : Fin n) : Euclidean N :=
  ((normalSpace F x).orthogonalProjectionOnto
    (fderiv ℝ (fun y ↦ partialDeriv F y j) x (EuclideanSpace.single i 1)) :
      Euclidean N)

/-- The normal map B_F(H) = ∑ H_ij II_ij. -/
def normalMap {n N : ℕ} (F : Euclidean n → Euclidean N) (x : Euclidean n)
    (H : MetricTensor n) : Euclidean N :=
  ∑ i, ∑ j, H i j • secondFundamentalForm F x i j

/-- Full normal rank means that the range of B_F is the normal space. -/
def HasFullNormalRankOn {n N : ℕ} (F : Euclidean n → Euclidean N)
    (s : Set (Euclidean n)) : Prop :=
  ∀ x ∈ s, Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N))

/-- The stress space consists of symmetric tensors in the kernel of B_F. -/
def stressSpace {n N : ℕ} (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    Set (MetricTensor n) :=
  {H | H.IsSymm ∧ normalMap F x H = 0}

/-- Equation main:eq:metric-expansion: the exact quadratic metric expansion. -/
theorem inducedMetric_add {n N : ℕ} {F Y : Euclidean n → Euclidean N}
    {x : Euclidean n} (hF : DifferentiableAt ℝ F x) (hY : DifferentiableAt ℝ Y x) :
    inducedMetric (F + Y) x =
      inducedMetric F x + linearizedMetric F Y x + inducedMetric Y x := by
  ext i j
  simp only [inducedMetric, linearizedMetric, partialDeriv, fderiv_add hF hY,
    add_apply, inner_add_left, inner_add_right, Matrix.add_apply]
  ac_rfl

/-- A positive definite induced metric makes the differential injective. -/
theorem isImmersionOn_of_isIsometricOn {n N : ℕ} {g : MetricField n}
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    (hg : ∀ x ∈ s, (g x).PosDef) (hF : IsIsometricOn g F s) :
    IsImmersionOn F s := by
  intro x hx
  refine (injective_iff_map_eq_zero _).2 ?_
  intro v hv
  have hmetric : (inducedMetric F x).PosDef := (hF hx).symm ▸ hg x hx
  have hsum : ∑ j, v j • partialDeriv F x j = fderiv ℝ F x v := by
    simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply, partialDeriv] using
      congrArg (fderiv ℝ F x) ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v)
  have hzero : (inducedMetric F x).mulVec (fun i ↦ v i) = 0 := by
    ext i
    change ∑ j, inner ℝ (partialDeriv F x i) (partialDeriv F x j) * v j = 0
    simpa only [inner_sum, inner_smul_right, inner_zero_right, mul_comm] using
      congrArg (fun w ↦ inner ℝ (partialDeriv F x i) w) (hsum.trans hv)
  have hcoeff : (fun i ↦ v i) = 0 := hmetric.mulVec_injective (by simpa using hzero)
  ext i
  exact congrFun hcoeff i

end JanetCartan
