module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.RealVector.Diagonal

/-!
# Actual real Euclidean image operators

Bounded real vector realizations of the published complex inverse and kernel
remainder, with coordinate identities and literal Hilbert adjoints, for
`app:ch_background:prop:bg-frame`, Step 1.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff ComplexInnerProductSpace
open JanetCartan.AmplitudeBound

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ} {I : Type*} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)
local notation "R²" => Lp (EuclideanSpace ℝ I) 2 (volume : Measure E)

/-- The Euclidean complex image inverse is literally self-adjoint
(`app:ch_background:defn:bg-row`), by its real symbol and Plancherel. -/
theorem imageBesselL2Operator_adjoint :
    (imageBesselL2Operator (d := d)).adjoint = imageBesselL2Operator := by
  let a := memLp_top_complex_imageBesselSymbol (d := d) |>.toLp _
  let M := multiplicationOperator a
  have hm (u v : L²) : ⟪M u, v⟫ = ⟪u, M v⟫ := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [multiplicationOperator_coeFn a u, multiplicationOperator_coeFn a v,
      memLp_top_complex_imageBesselSymbol.coeFn_toLp] with x hx hy ha
    change inner ℂ (M u x) (v x) = inner ℂ (u x) (M v x)
    change M u x = a x * u x at hx
    change M v x = a x * v x at hy
    rw [hx, hy]
    change a x = (imageBesselSymbol x : ℂ) at ha
    rw [ha]
    simp [mul_comm, mul_left_comm, mul_assoc]
  apply IsSelfAdjoint.adjoint_eq
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro u v
  change ⟪imageBesselL2Operator u, v⟫ = ⟪u, imageBesselL2Operator v⟫
  let e := Lp.fourierTransformₗᵢ E ℂ
  rw [← e.inner_map_map (imageBesselL2Operator u) v,
    ← e.inner_map_map u (imageBesselL2Operator v)]
  change ⟪e (e.symm (M (e u))), e v⟫ = ⟪e u, e (e.symm (M (e v)))⟫
  simpa only [e.apply_symm_apply] using hm (e u) (e v)

/-- The actual real vector Euclidean Bessel inverse for the image channel
(`app:ch_background:defn:bg-row`). -/
def realImageBesselL2Operator : R² →L[ℝ] R² :=
  realImageDiagonalL2Operator imageBesselL2Operator

/-- Each complexified real coordinate has exactly the published Euclidean
scalar action (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem complexifiedL2Coordinate_realImageBesselL2Operator (u : R²) (i : I) :
    complexifiedL2Coordinate volume i (realImageBesselL2Operator u) =
      imageBesselL2Operator (complexifiedL2Coordinate volume i u) :=
  complexifiedL2Coordinate_realImageDiagonalL2Operator _
    imageBesselL2Operator_realProjection u i

/-- Literal real Hilbert adjoint of the image inverse
(`app:ch_background:defn:bg-row`). -/
theorem realImageBesselL2Operator_adjoint :
    (realImageBesselL2Operator (d := d) (I := I)).adjoint = realImageBesselL2Operator := by
  rw [realImageBesselL2Operator, realImageDiagonalL2Operator_adjoint,
    imageBesselL2Operator_adjoint]

/-- The actual bounded real vector realization of the localized image remainder
(`app:ch_background:prop:bg-frame`, Step 1). -/
def realLocalizedImageBesselRemainderOperator
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r) : R² →L[ℝ] R² :=
  realImageDiagonalL2Operator
    (localizedImageBesselRemainderOperator hr χ ψ hχ hψ hχs hψs)

/-- Exact scalar coordinate action of the real remainder, with all reality
premises discharged from its real kernel
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem complexifiedL2Coordinate_realLocalizedImageBesselRemainderOperator
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r)
    (u : R²) (i : I) :
    complexifiedL2Coordinate volume i
      (realLocalizedImageBesselRemainderOperator hr χ ψ hχ hψ hχs hψs u) =
    localizedImageBesselRemainderOperator hr χ ψ hχ hψ hχs hψs
      (complexifiedL2Coordinate volume i u) :=
  complexifiedL2Coordinate_realImageDiagonalL2Operator _
    (localizedImageBesselRemainderOperator_realProjection hr χ ψ hχ hψ hχs hψs) u i

/-- The literal real Hilbert adjoint swaps the actual remainder masks,
using the proved reversal of its kernel
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realLocalizedImageBesselRemainderOperator_adjoint
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r) :
    (realLocalizedImageBesselRemainderOperator (I := I) hr χ ψ hχ hψ hχs hψs).adjoint =
      realLocalizedImageBesselRemainderOperator hr ψ χ hψ hχ hψs hχs := by
  rw [realLocalizedImageBesselRemainderOperator, realImageDiagonalL2Operator_adjoint,
    localizedImageBesselRemainderOperator_adjoint]
  rfl

end JanetCartan.ContinuumNormalReduction.ImageNormal
