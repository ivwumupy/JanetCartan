module

public import JanetCartan.Analysis.Microlocal.NormalComparison.MatrixColumns.Kernels

/-!
# Matrix inputs with the original coordinate output

The full normal construction in `app:ch_osc:prop:osc-normal` uses the
coordinate Hilbert-sum output.  This kernel identity keeps that output
and the original restricted input measure, while realizing its rectangular
matrix integral on the entire native vector L² input.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace JanetCartan.NormalComparison

variable {X Y I J : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype I] [Fintype J]

/-- Literal matrix kernel for the unchanged coordinate output of the full
normal construction (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem matrixColumnOperator_ae_component_integral (μ : Measure X) (ν : Measure Y)
    (T : J → Lp ℂ 2 μ →L[ℂ] PiLp 2 (fun _ : I ↦ Lp ℂ 2 ν))
    (K : J → I → Y → X → ℂ)
    (hT : ∀ j (g : Lp ℂ 2 μ) i, (T j g) i =ᵐ[ν] fun y ↦ ∫ x, g x * K j i y x ∂μ)
    (hK : ∀ j (g : Lp ℂ 2 μ) i y, Integrable (fun x ↦ g x * K j i y x) μ)
    (f : Lp (EuclideanSpace ℂ J) 2 μ) (i : I) :
    (matrixColumnOperator μ T f) i =ᵐ[ν] fun y ↦ ∫ x, ∑ j, f x j * K j i y x ∂μ := by
  rw [matrixColumnOperator_apply]
  have heq : (∑ j, T j (Pseudodifferential.finiteL2CoordinateIsometry μ f j)) i =
      ∑ j, T j (Pseudodifferential.finiteL2CoordinateIsometry μ f j) i := by
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
  rw [heq]
  have hint (j : J) (y : Y) : Integrable (fun x ↦ f x j * K j i y x) μ := by
    apply (hK j (Pseudodifferential.finiteL2CoordinateIsometry μ f j) i y).congr
    filter_upwards [Pseudodifferential.finiteL2Coordinates_apply_ae μ f j] with x hx
    change Pseudodifferential.finiteL2CoordinateIsometry μ f j x = f x j at hx
    rw [hx]
  have hall := ae_all_iff.mpr (fun j ↦
    hT j (Pseudodifferential.finiteL2CoordinateIsometry μ f j) i)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun j ↦ T j (Pseudodifferential.finiteL2CoordinateIsometry μ f j) i), hall] with y hy hty
  rw [hy, integral_finsetSum _ (fun j _ ↦ hint j y)]
  apply Finset.sum_congr rfl
  intro j _
  rw [hty j]
  apply integral_congr_ae
  filter_upwards [Pseudodifferential.finiteL2Coordinates_apply_ae μ f j] with x hx
  change Pseudodifferential.finiteL2CoordinateIsometry μ f j x = f x j at hx
  rw [hx]

end JanetCartan.NormalComparison
