module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector
public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization.Normal
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.Blocks

/-!
# Agreement with the graph normal Hilbert operators

The scalar-to-matrix bounds of `app:ch_regular_base:eq:fio-input` apply to the
already published graph normal operators, with precisely the same Lebesgue
measure, finite Hilbert norms, and literal adjoints.
-/

@[expose] public noncomputable section
open MeasureTheory
open JanetCartan.AmplitudeBound
namespace JanetCartan.Pseudodifferential
variable {d : ℕ} {I J : Type*} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- Coordinate extraction commutes with scalar insertion into vector L²,
for `app:ch_regular_base:eq:fio-input`. -/
theorem finiteL2Coordinates_injection (i : I) (f : L²) :
    finiteL2Coordinates volume
      ((coordinateInjection i : ℂ →ₗᵢ[ℂ] EuclideanSpace ℂ I).toContinuousLinearMap.compLpL 2 volume f) =
        coordinateInjection i f := by
  classical
  apply PiLp.ext
  intro k
  apply Lp.ext
  have he := (coordinateInjection i : ℂ →ₗᵢ[ℂ] EuclideanSpace ℂ I).toContinuousLinearMap.coeFn_compLpL f
  have hp := finiteL2Coordinates_apply_ae volume
    ((coordinateInjection i : ℂ →ₗᵢ[ℂ] EuclideanSpace ℂ I).toContinuousLinearMap.compLpL 2 volume f) k
  by_cases hk : k = i
  · subst k
    filter_upwards [hp, he] with x hx hy
    simpa [coordinateInjection] using hx.trans (congrArg (fun z : EuclideanSpace ℂ I ↦ z i) hy)
  · have hz := Lp.coeFn_zero ℂ 2 (volume : Measure E)
    filter_upwards [hp, he, hz] with x hx hy hz
    simpa [coordinateInjection, Pi.single_apply, hk, hz] using
      hx.trans (congrArg (fun z : EuclideanSpace ℂ I ↦ z k) hy)

/-- The isometrically assembled operator is exactly the finite sum of literal
vector coordinate operators (`app:ch_regular_base:thm:actual-calculus`). -/
theorem vectorMatrixL2Operator_eq_sum (B : I → J → L² →L[ℂ] L²) :
    vectorMatrixL2Operator B =
      ∑ i, ∑ j, ((coordinateInjection i : ℂ →ₗᵢ[ℂ] EuclideanSpace ℂ I).toContinuousLinearMap.compLpL 2 volume).comp
        ((B i j).comp ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : J ↦ ℂ) j).compLpL 2 volume)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (finiteL2CoordinateIsometry volume).injective
  rw [finiteL2CoordinateIsometry_vectorMatrixL2Operator]
  change matrixOperator B (finiteL2Coordinates volume f) = finiteL2Coordinates volume _
  simp only [sum_apply, ContinuousLinearMap.comp_apply, map_sum, finiteL2Coordinates_injection]
  apply PiLp.ext
  intro i
  classical
  simp [matrixOperator_apply, coordinateInjection, Pi.single_apply, finiteL2Coordinates]

/-- Agreement with the graph normal's previously defined vector operator,
for `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem vectorMatrixL2Operator_eq_graphMatrixL2Operator {r : ℕ}
    (B : Fin r → Fin r → L² →L[ℂ] L²) :
    vectorMatrixL2Operator B = FourierIntegral.graphMatrixL2Operator B := by
  rw [vectorMatrixL2Operator_eq_sum]
  rfl

/-- Agreement with the graph normal's direct-sum block operator,
for `app:ch_regular_base:eq:actual-normal-kernel`. -/
theorem matrixOperator_eq_normalKernel_blocks {r : ℕ}
    (B : Fin r → Fin r → L² →L[ℂ] L²) :
    matrixOperator B = FourierIntegral.NormalKernel.blocks B := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro i
  rw [matrixOperator_apply, FourierIntegral.NormalKernel.blocks_apply]

end JanetCartan.Pseudodifferential
