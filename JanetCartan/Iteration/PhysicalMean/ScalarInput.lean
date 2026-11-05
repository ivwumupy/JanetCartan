module

public import JanetCartan.Iteration.PhysicalMean.CurrentAdjoint

/-!
# The original scalar raw input and its exact matrix-coordinate realization

The native sampled kernel has scalar complex input, regarded as real for
`2 Re`. The matrix moment proof uses a singleton input coordinate solely to
assemble its fixed measured output coordinates. The identities below remove
that bookkeeping coordinate from the SAME actual adjoint, with no input
measure change, dimension factor or replacement row
(`app:ch_mean_pairs:eq:raw-adjoint-moments`).
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.PhysicalMean

open Pseudodifferential PeriodicLocalL2 AmplitudeBound.PaperEstimates

variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype I]

/-- The scalar raw adjoint is exactly the singleton coordinate of the native
matrix adjoint whenever the original forward coordinates agree. No scalar
raw input is replaced by a genuinely larger Hilbert space. -/
theorem nativeScalarRow_adjoint_eq_matrixCoordinate
    (μ : Measure X) (ν : Measure Y)
    (B : I → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν)
    (A : Lp ℂ 2 μ →L[ℂ] Lp (EuclideanSpace ℂ I) 2 ν)
    (hA : ∀ f i, finiteL2CoordinateIsometry ν (A f) i = B i f)
    (u : Lp (EuclideanSpace ℂ I) 2 ν) :
    A.adjoint u = finiteL2CoordinateIsometry μ
      ((nativeMatrixRowOperator μ ν (fun i (_ : Unit) ↦ B i)).adjoint u) () := by
  rw [nativeSampledMatrixRow_adjoint, nativeMatrixRowOperator_coordinate]
  apply ext_inner_left ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right,
    ← (finiteL2CoordinateIsometry ν).inner_map_map, PiLp.inner_apply, inner_sum]
  simp only [hA, ContinuousLinearMap.adjoint_inner_right]

omit [MeasurableSpace Y] [Fintype I] in
/-- The original periodic real scalar-input row keeps the same adjoint after
removing the artificial singleton coordinate in the matrix calculation.
Both genuine real quadratures and their factor two are retained. -/
theorem nativeRealScalarRow_adjoint_eq_matrixCoordinate {n : ℕ}
    (μ : Measure X)
    (B : Fin n → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (A : Lp ℂ 2 μ →L[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hA : ∀ f i, finiteL2CoordinateIsometry volume (A f) i = B i f)
    (u : ContinuumRow.OutputL2 n) :
    (transferOutputOperator (realQuadratureChannel A)).adjoint u =
      finiteL2CoordinateIsometry μ
        ((transferOutputOperator (realQuadratureChannel
          (nativeMatrixRowOperator μ volume (fun i (_ : Unit) ↦ B i)))).adjoint u) () := by
  simp only [transferOutputOperator_adjoint, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, realQuadratureChannel_adjoint_apply]
  rw [nativeScalarRow_adjoint_eq_matrixCoordinate μ volume B A hA]
  exact (congrArg (fun z : PiLp 2 (fun _ : Unit ↦ Lp ℂ 2 μ) ↦ z ())
    (LinearMapClass.map_smul_of_tower (finiteL2CoordinateIsometry μ) (2 : ℝ) _)).symm

end JanetCartan.PhysicalMean
