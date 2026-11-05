module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowApplication.Matrices.Assembly

/-!
# Literal original matrix row kernels

The native rectangular matrix row in `app:ch_osc:lem:osc-amplitude` is
reassembled from the actual scalar row kernels. Boundedness and measurability
of the original amplitude prove the finite integral interchanges; no matrix
kernel identity is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace JanetCartan.AmplitudeBound.PaperEstimates

open Pseudodifferential

variable {X Y I J : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype I] [Fintype J]

/-- Actual scalar-entry kernels imply the literal native matrix integral
for the same datum. The original bounded amplitude and native kernel
integrability justify every finite sum and integral interchange
(`app:ch_osc:lem:osc-amplitude`). -/
theorem nativeMatrixRowOperator_ae_kernel_of_entries (μ : Measure X) (ν : Measure Y)
    (B : I → J → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν) (b : X → Y → Matrix I J ℂ)
    (hb : ∀ i j, StronglyMeasurable (fun q : X × Y ↦ b q.1 q.2 i j))
    (A : ℝ) (hbound : ∀ u y i j, ‖b u y i j‖ ≤ A)
    (K : Y → X → ℂ) (f : Lp (EuclideanSpace ℂ J) 2 μ)
    (hK : ∀ᵐ y ∂ν, Integrable (fun u ↦ K y u • f u) μ)
    (hB : ∀ i j, B i j (finiteL2CoordinateIsometry μ f j) =ᵐ[ν]
      fun y ↦ ∫ u, b u y i j * K y u * finiteL2CoordinateIsometry μ f j u ∂μ) :
    nativeMatrixRowOperator μ ν B f =ᵐ[ν] fun y ↦
      ∫ u, K y u • WithLp.toLp 2 ((b u y).mulVec (f u).ofLp) ∂μ := by
  apply (finiteL2CoordinateIsometry_ae_iff ν _ _).mpr
  intro i
  rw [nativeMatrixRowOperator_coordinate]
  have hall := ae_all_iff.mpr (hB i)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun j ↦ B i j (finiteL2CoordinateIsometry μ f j)), hall, hK] with y hy hby hky
  have hint (i' : I) (j : J) :
      Integrable (fun u ↦ K y u * (b u y i' j * f u j)) μ := by
    have hk := hky.eval_piLp j
    change Integrable (fun u ↦ K y u * f u j) μ at hk
    have hbj : AEStronglyMeasurable (fun u ↦ b u y i' j) μ :=
      ((hb i' j).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    apply (hk.bdd_mul hbj (Eventually.of_forall (fun u ↦ hbound u y i' j))).congr
    filter_upwards with u
    change b u y i' j * (K y u * f u j) = K y u * (b u y i' j * f u j)
    ring
  have hvec : ∀ i' : I, Integrable
      (fun u ↦ (K y u • WithLp.toLp 2 ((b u y).mulVec (f u).ofLp) : EuclideanSpace ℂ I) i') μ := by
    intro i'
    change Integrable (fun u ↦ K y u * (∑ j, b u y i' j * f u j)) μ
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ (fun j _ ↦ hint i' j)
  rw [hy, eval_integral_piLp hvec i]
  change (∑ j, B i j (finiteL2CoordinateIsometry μ f j) y) =
    ∫ u, K y u * (∑ j, b u y i j * f u j) ∂μ
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ ↦ hint i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [hby j]
  apply integral_congr_ae
  filter_upwards [finiteL2Coordinates_apply_ae μ f j] with u hu
  change finiteL2CoordinateIsometry μ f j u = f u j at hu
  change b u y i j * K y u * finiteL2CoordinateIsometry μ f j u =
    K y u * (b u y i j * f u j)
  rw [hu]
  ring

end JanetCartan.AmplitudeBound.PaperEstimates
