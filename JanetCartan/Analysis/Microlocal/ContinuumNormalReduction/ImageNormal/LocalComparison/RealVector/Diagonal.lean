module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.RealVector.Coordinates
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.RealVector.EuclideanReality
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector
public import JanetCartan.Analysis.Operator.RealQuadratures

/-!
# Real diagonal realization of the scalar image operators

The existing finite coordinate isometry and real compression construct the
vector operators needed by `app:ch_background:prop:bg-frame`, Step 1.
The two consumers are the Euclidean image inverse and its localized remainder.
-/

@[expose] public noncomputable section
open MeasureTheory
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ} {I : Type*} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)
local notation "P" => imageScalarRealProjection.compLpL 2 (volume : Measure E)

/-- Diagonal complex realization used for the two image operators in
`app:ch_background:prop:bg-frame`, Step 1. -/
def imageDiagonalL2Operator (A : L² →L[ℂ] L²) :
    Lp (EuclideanSpace ℂ I) 2 (volume : Measure E) →L[ℂ]
      Lp (EuclideanSpace ℂ I) 2 (volume : Measure E) := by
  classical
  exact vectorMatrixL2Operator (fun i j : I ↦ if i = j then A else 0)

/-- Real vector realization used for the inverse and remainder of
`app:ch_background:defn:bg-row`. -/
def realImageDiagonalL2Operator (A : L² →L[ℂ] L²) :
    Lp (EuclideanSpace ℝ I) 2 (volume : Measure E) →L[ℝ]
      Lp (EuclideanSpace ℝ I) 2 (volume : Measure E) :=
  realOutputCompression (imageDiagonalL2Operator A)

/-- Coordinates of the complex diagonal realization
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coordinate_imageDiagonalL2Operator (A : L² →L[ℂ] L²)
    (u : Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)) (i : I) :
    finiteL2CoordinateIsometry volume (imageDiagonalL2Operator A u) i =
      A (finiteL2CoordinateIsometry volume u i) := by
  classical
  simp only [imageDiagonalL2Operator, finiteL2CoordinateIsometry_vectorMatrixL2Operator,
    matrixOperator_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem coordinate_inclusion
    (u : Lp (EuclideanSpace ℝ I) 2 (volume : Measure E)) (i : I) :
    finiteL2CoordinateIsometry volume (l2ComplexInclusion volume u) i =
      complexifiedL2Coordinate volume i u := by
  apply Lp.ext
  filter_upwards [finiteL2Coordinates_apply_ae volume (l2ComplexInclusion volume u) i,
    euclideanComplexInclusion.coeFn_compLpL u,
    complexifiedL2Coordinate_coe volume i u] with x hx hy hz
  exact hx.trans ((congrArg (fun v : EuclideanSpace ℂ I ↦ v i) hy).trans hz.symm)

private theorem coordinate_realPart
    (u : Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)) (i : I) :
    complexifiedL2Coordinate volume i (l2RealPart volume u) =
      P (finiteL2CoordinateIsometry volume u i) := by
  apply Lp.ext
  filter_upwards [complexifiedL2Coordinate_coe volume i (l2RealPart volume u),
    euclideanRealPart.coeFn_compLpL u,
    imageScalarRealProjection.coeFn_compLpL (finiteL2CoordinateIsometry volume u i),
    finiteL2Coordinates_apply_ae volume u i] with x hx hy hz hw
  change _ = imageScalarRealProjection _ at hz
  change l2RealPart volume u x = euclideanRealPart (u x) at hy
  change finiteL2CoordinateIsometry volume u i x = u x i at hw
  rw [hx, hy, hz, hw]
  rfl

/-- Coordinate complexification is already real, for the concrete image
realizations (`app:ch_background:defn:bg-row`). -/
theorem realProjection_complexifiedL2Coordinate
    (u : Lp (EuclideanSpace ℝ I) 2 (volume : Measure E)) (i : I) :
    P (complexifiedL2Coordinate volume i u) = complexifiedL2Coordinate volume i u := by
  apply Lp.ext
  filter_upwards [imageScalarRealProjection.coeFn_compLpL (complexifiedL2Coordinate volume i u),
    complexifiedL2Coordinate_coe volume i u] with x hx hy
  rw [hx, hy]
  rfl

/-- Coordinate identity for a real-preserving scalar image operator.
The concrete producers are `imageBesselL2Operator_realProjection` and
`localizedImageBesselRemainderOperator_realProjection`
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem complexifiedL2Coordinate_realImageDiagonalL2Operator (A : L² →L[ℂ] L²)
    (hA : ∀ f, P (A f) = A (P f))
    (u : Lp (EuclideanSpace ℝ I) 2 (volume : Measure E)) (i : I) :
    complexifiedL2Coordinate volume i (realImageDiagonalL2Operator A u) =
      A (complexifiedL2Coordinate volume i u) := by
  change complexifiedL2Coordinate volume i
    (l2RealPart volume (imageDiagonalL2Operator A (l2ComplexInclusion volume u))) = _
  rw [coordinate_realPart, coordinate_imageDiagonalL2Operator, coordinate_inclusion,
    hA, realProjection_complexifiedL2Coordinate]

/-- Diagonal realization respects the literal complex Hilbert adjoint
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageDiagonalL2Operator_adjoint (A : L² →L[ℂ] L²) :
    (imageDiagonalL2Operator (I := I) A).adjoint = imageDiagonalL2Operator A.adjoint := by
  classical
  rw [imageDiagonalL2Operator, vectorMatrixL2Operator_adjoint, imageDiagonalL2Operator]
  congr 1
  funext i j
  by_cases h : i = j
  · subst j; simp
  · simp [h, Ne.symm h]

/-- Real compression retains the literal Hilbert adjoint, with no reality
premise (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realImageDiagonalL2Operator_adjoint (A : L² →L[ℂ] L²) :
    (realImageDiagonalL2Operator (I := I) A).adjoint =
      realImageDiagonalL2Operator A.adjoint := by
  have hi : (l2ComplexInclusion (ι := I) (volume : Measure E)).adjoint = l2RealPart volume := by
    rw [← l2RealPart_adjoint, ContinuousLinearMap.adjoint_adjoint]
  simp only [realImageDiagonalL2Operator, realOutputCompression,
    ContinuousLinearMap.adjoint_comp, hi, l2RealPart_adjoint,
    adjoint_restrictScalars_complex, imageDiagonalL2Operator_adjoint,
    ContinuousLinearMap.comp_assoc]

end JanetCartan.ContinuumNormalReduction.ImageNormal
