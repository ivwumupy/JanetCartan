module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowApplication.Matrices.Assembly
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Realization.CompactKernel
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.CompactSupport

/-!
# Actual adjoints of native sampled matrix kernels

The source measure in `app:ch_mean_pairs:eq:raw-adjoint-moments` is the SAME
finite disjoint-shell measure as the scalar auxiliary test. The matrix row
uses its native vector-valued L² input. The statements below derive its
Hilbert adjoint from its forward kernel, by the existing compact scalar
Fubini theorem and exact coordinate isometries. No adjoint-kernel formula
is assumed and no alternative adjoint is selected.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace JanetCartan.PhysicalMean

open Pseudodifferential AmplitudeBound.PaperEstimates
open ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel

variable {X Y I J : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype I] [Fintype J]

/-- The adjoint of the ORIGINAL native matrix row reverses the finite matrix
indices on the SAME two measures (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem nativeSampledMatrixRow_adjoint (μ : Measure X) (ν : Measure Y)
    (B : I → J → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν) :
    (nativeMatrixRowOperator μ ν B).adjoint =
      nativeMatrixRowOperator ν μ (fun j i ↦ (B i j).adjoint) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [← (finiteL2CoordinateIsometry (I := I) ν).inner_map_map,
    ← (finiteL2CoordinateIsometry (I := J) μ).inner_map_map]
  simp only [PiLp.inner_apply, nativeMatrixRowOperator_coordinate,
    sum_inner, inner_sum, ContinuousLinearMap.adjoint_inner_right]
  exact Finset.sum_comm

variable [MetricSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MetricSpace Y] [BorelSpace Y]

/-- The actual native matrix adjoint has the original conjugated kernel in
each source coordinate. Compact supports prove every integral and Fubini
premise; the input need not be a smooth test function
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem nativeSampledMatrixRow_adjoint_coordinate_kernel
    (μ : Measure X) (ν : Measure Y) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    [SFinite μ] [SFinite ν]
    (B : I → J → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν) (K : I → J → Y → X → ℂ)
    (hKc : ∀ i j, Continuous (Function.uncurry (K i j)))
    (hKs : ∀ i j, HasCompactSupport (Function.uncurry (K i j)))
    (hB : ∀ i j (g : Lp ℂ 2 μ), B i j g =ᵐ[ν] fun x ↦ ∫ z, K i j x z * g z ∂μ)
    (v : Lp (EuclideanSpace ℂ I) 2 ν) (j : J) :
    finiteL2CoordinateIsometry μ ((nativeMatrixRowOperator μ ν B).adjoint v) j =ᵐ[μ]
      fun z ↦ ∑ i, ∫ x, star (K i j x z) * finiteL2CoordinateIsometry ν v i x ∂ν := by
  rw [nativeSampledMatrixRow_adjoint, nativeMatrixRowOperator_coordinate]
  have ha := ae_all_iff.mpr (fun i ↦ adjoint_eq_integral_of_compactKernel
    (hKc i j) (hKs i j) (B i j) (hB i j) (finiteL2CoordinateIsometry ν v i))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i ↦ (B i j).adjoint (finiteL2CoordinateIsometry ν v i)), ha] with z hz he
  exact hz.trans (Finset.sum_congr rfl (fun i _ ↦ he i))

/-- A scalar entry of the ORIGINAL sampled row has the literal chart
adjoint used by the moment trade. Its initial frequency mask and square-root
sample weight stay in `m`, outside physical integration by parts. The same
kernel and datum are retained (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem sampledScalarRow_adjoint_ae_chart {n : ℕ}
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (K : Euclidean n → X → ℂ)
    (hKc : Continuous (Function.uncurry K)) (hKs : HasCompactSupport (Function.uncurry K))
    (hS : ∀ g : Lp ℂ 2 μ, S g =ᵐ[volume] fun x ↦ ∫ z, K x z * g z ∂μ)
    (m : X → ℝ) (φ : X → Euclidean n → ℝ)
    (a : X → Euclidean n → ℂ)
    (hK : ∀ x z, K x z = (m z : ℂ) * NormalComparison.oscillatoryFactor 1 (φ z x) * star (a z x))
    (v : Euclidean n → ℂ) (hv : MemLp v 2 volume) :
    S.adjoint (hv.toLp v) =ᵐ[μ] fun z ↦ (m z : ℂ) *
      ContinuumAdjoint.DerivativeKernels.chartAdjoint (φ z) (a z) v := by
  have hadj := adjoint_eq_integral_of_compactKernel hKc hKs S hS (hv.toLp v)
  filter_upwards [hadj] with z hz
  rw [hz]
  have he : (∫ x, star (K x z) * (hv.toLp v) x) = ∫ x, star (K x z) * v x := by
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp] with x hx
    rw [hx]
  rw [he]
  simpa only [ContinuumAdjoint.DerivativeKernels.modifiedCarrierKernel, ← hK] using
    ContinuumAdjoint.DerivativeKernels.integral_star_modifiedCarrierKernel
      (fun _ x _ ↦ φ z x) (fun _ x _ ↦ a z x) (fun _ ↦ m z) v (0, 0)

end JanetCartan.PhysicalMean
