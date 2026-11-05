module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowApplication.Matrices.Kernel
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowApplication.Matrices.PointwiseSobolev
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowApplication.PhysicalSobolev

/-!
# The original physical Sobolev estimate for fixed matrix rows

The fixed-matrix clause of `app:ch_osc:eq:amplitude-row` follows from the
actual scalar operators on the same measure and the same original `T`.
The input norm is exactly the physical `H^ell` norm with weight
`<2*pi*xi>^ell`. Only the continuous Sobolev representative is used; no
finite or infinite physical derivative hypothesis is added.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter FourierTransform
open scoped ENNReal

namespace JanetCartan.AmplitudeBound.PaperEstimates

open Pseudodifferential FourierConventions

variable {d : ℕ} {X I J : Type*} [MeasurableSpace X] [Fintype I] [Fintype J] {μ : Measure X}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Output" => Lp ℂ 2 (volume : Measure E)

variable (R : ℝ) (b : X → EuclideanSpace ℝ (Fin d) → Matrix I J ℂ)
  (hb : ∀ i j, StronglyMeasurable (fun q : X × EuclideanSpace ℝ (Fin d) ↦ b q.1 q.2 i j))
  (hc : ∀ i j u, Continuous (fun x ↦ b u x i j))
  (hs : ∀ i j u, SupportedInCenteredBox R (fun x ↦ b u x i j))
  (hm : ∀ i j u, MemLp (fun x ↦ b u x i j) 2 volume)
  (hphys : ∀ i j u, MemLp (fun ξ ↦ euclideanSobolevWeight (d / 2 + 1 : ℕ)
    ((2 * Real.pi) • ξ) • (𝓕 ((hm i j u).toLp (fun x ↦ b u x i j)) :
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) ξ) 2 volume)
  (A : ℝ) (hA : 0 ≤ A)
  (hbound : ∀ i j u, (eLpNorm (fun ξ ↦ euclideanSobolevWeight (d / 2 + 1 : ℕ)
    ((2 * Real.pi) • ξ) • (𝓕 ((hm i j u).toLp (fun x ↦ b u x i j)) :
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) ξ) 2 volume).toReal ≤ A)

/-- The actual native matrix row, constructed by applying the checked
scalar Sobolev row to every original matrix entry and to the same `T`
(`app:ch_osc:lem:osc-amplitude`). -/
def physicalSobolevMatrixRowAmplitudeOperator (T : Lp ℂ 2 μ →L[ℂ] Output) :
    Lp (EuclideanSpace ℂ J) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ I) 2 (volume : Measure E) :=
  nativeMatrixRowOperator μ volume (fun i j ↦
    compactRowAmplitudeOperator R (fun u x ↦ b u x i j) (hb i j) (hs i j) (hm i j)
      (fun u ↦ (fourierSobolev_of_physical_weight (d / 2 + 1)
        ((hm i j u).toLp (fun x ↦ b u x i j)) (hphys i j u)).1)
      A hA (fun u ↦ (fourierSobolev_of_physical_weight (d / 2 + 1)
        ((hm i j u).toLp (fun x ↦ b u x i j)) (hphys i j u)).2.trans (hbound i j u)) T)

/-- The physical Sobolev row bound for the actual native rectangular
matrix operator, with only fixed rank factors
(`app:ch_osc:eq:amplitude-row`). -/
theorem norm_physicalSobolevMatrixRowAmplitudeOperator_le (T : Lp ℂ 2 μ →L[ℂ] Output) :
    ‖physicalSobolevMatrixRowAmplitudeOperator R b hb hs hm hphys A hA hbound T‖ ≤
      ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * rowAmplitudeConstant d R) * ‖T‖ * A := by
  unfold physicalSobolevMatrixRowAmplitudeOperator
  apply (norm_nativeMatrixRowOperator_le_of_entry_bound μ volume _
    (rowAmplitudeConstant d R * ‖T‖ * A) ?_).trans_eq
  · ring
  · intro i j
    exact norm_compactRowAmplitudeOperator_le R (fun u x ↦ b u x i j) (hb i j) (hs i j) (hm i j)
      (fun u ↦ (fourierSobolev_of_physical_weight (d / 2 + 1)
        ((hm i j u).toLp (fun x ↦ b u x i j)) (hphys i j u)).1)
      A hA (fun u ↦ (fourierSobolev_of_physical_weight (d / 2 + 1)
        ((hm i j u).toLp (fun x ↦ b u x i j)) (hphys i j u)).2.trans (hbound i j u)) T

include hc in
/-- The original physical Sobolev matrix row has the literal matrix
kernel on its natural integrable L² core. The needed pointwise domination
is derived from the same Sobolev row, not supplied separately
(`app:ch_osc:eq:amplitude-row`). -/
theorem physicalSobolevMatrixRowAmplitudeOperator_ae_kernel_on_L1_core
    (T : Lp ℂ 2 μ →L[ℂ] Output) (K : E → X → ℂ)
    (hT : ∀ g : Lp ℂ 2 μ, Integrable (g : X → ℂ) μ →
      T g =ᵐ[volume] fun x ↦ ∫ u, K x u * g u ∂μ)
    (f : Lp (EuclideanSpace ℂ J) 2 μ) (hf : Integrable (f : X → EuclideanSpace ℂ J) μ)
    (hK : ∀ᵐ x ∂volume, Integrable (fun u ↦ K x u • f u) μ) :
    physicalSobolevMatrixRowAmplitudeOperator R b hb hs hm hphys A hA hbound T f =ᵐ[volume]
      fun x ↦ ∫ u, K x u • WithLp.toLp 2 ((b u x).mulVec (f u).ofLp) ∂μ := by
  have hHs (i : I) (j : J) (u : X) := (fourierSobolev_of_physical_weight (d / 2 + 1)
    ((hm i j u).toLp (fun x ↦ b u x i j)) (hphys i j u)).1
  have hunit (i : I) (j : J) (u : X) := (fourierSobolev_of_physical_weight (d / 2 + 1)
    ((hm i j u).toLp (fun x ↦ b u x i j)) (hphys i j u)).2.trans (hbound i j u)
  apply nativeMatrixRowOperator_ae_kernel_of_entries μ volume _ b hb (rowAmplitudeConstant d R * A)
    (fun u x i j ↦ norm_rowAmplitude_le_of_sobolev R (fun u x ↦ b u x i j)
      (hc i j) (hs i j) (hm i j) (hHs i j) A hA (hunit i j) u x) K f hK
  intro i j
  apply compactRowAmplitudeOperator_ae_kernel_on_L1_core R (fun u x ↦ b u x i j)
    (hb i j) (hc i j) (hs i j) (hm i j) (hHs i j) A hA (hunit i j) T K hT
    (finiteL2CoordinateIsometry μ f j) (integrable_nativeRowCoordinate μ f hf j)
  filter_upwards [hK] with x hx
  exact integrable_nativeRowKernelCoordinate μ f (K x) hx j

include hc in
/-- The same original physical Sobolev matrix kernel on any L² datum
for which its original kernel action is absolutely integrable
(`app:ch_osc:eq:amplitude-row`). -/
theorem physicalSobolevMatrixRowAmplitudeOperator_ae_kernel
    (T : Lp ℂ 2 μ →L[ℂ] Output) (K : E → X → ℂ)
    (hT : ∀ g : Lp ℂ 2 μ, T g =ᵐ[volume] fun x ↦ ∫ u, K x u * g u ∂μ)
    (f : Lp (EuclideanSpace ℂ J) 2 μ)
    (hK : ∀ᵐ x ∂volume, Integrable (fun u ↦ K x u • f u) μ) :
    physicalSobolevMatrixRowAmplitudeOperator R b hb hs hm hphys A hA hbound T f =ᵐ[volume]
      fun x ↦ ∫ u, K x u • WithLp.toLp 2 ((b u x).mulVec (f u).ofLp) ∂μ := by
  have hHs (i : I) (j : J) (u : X) := (fourierSobolev_of_physical_weight (d / 2 + 1)
    ((hm i j u).toLp (fun x ↦ b u x i j)) (hphys i j u)).1
  have hunit (i : I) (j : J) (u : X) := (fourierSobolev_of_physical_weight (d / 2 + 1)
    ((hm i j u).toLp (fun x ↦ b u x i j)) (hphys i j u)).2.trans (hbound i j u)
  apply nativeMatrixRowOperator_ae_kernel_of_entries μ volume _ b hb (rowAmplitudeConstant d R * A)
    (fun u x i j ↦ norm_rowAmplitude_le_of_sobolev R (fun u x ↦ b u x i j)
      (hc i j) (hs i j) (hm i j) (hHs i j) A hA (hunit i j) u x) K f hK
  intro i j
  apply compactRowAmplitudeOperator_ae_kernel R (fun u x ↦ b u x i j)
    (hb i j) (hc i j) (hs i j) (hm i j) (hHs i j) A hA (hunit i j) T K
    (finiteL2CoordinateIsometry μ f j)
  · filter_upwards [hK] with x hx
    exact integrable_nativeRowKernelCoordinate μ f (K x) hx j
  · intro k
    exact hT _

include hb hc hs hm hphys hA hbound in
/-- The fixed-matrix physical `H^ell` clause of
`app:ch_osc:lem:osc-amplitude`, on the original native vector L² spaces.
The operator and its kernel are actually constructed from the original
Sobolev rows, without an additional physical derivative hypothesis. -/
theorem exists_matrixRowAmplitudeOperator_of_physicalSobolev
    (T : Lp ℂ 2 μ →L[ℂ] Output) :
    ∃ S : Lp (EuclideanSpace ℂ J) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ I) 2 (volume : Measure E),
      ‖S‖ ≤ ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * rowAmplitudeConstant d R) * ‖T‖ * A ∧
      ∀ (K : E → X → ℂ),
        (∀ g : Lp ℂ 2 μ, Integrable (g : X → ℂ) μ →
          T g =ᵐ[volume] fun x ↦ ∫ u, K x u * g u ∂μ) →
        ∀ (f : Lp (EuclideanSpace ℂ J) 2 μ), Integrable (f : X → EuclideanSpace ℂ J) μ →
          (∀ᵐ x ∂volume, Integrable (fun u ↦ K x u • f u) μ) →
            S f =ᵐ[volume] fun x ↦ ∫ u, K x u • WithLp.toLp 2 ((b u x).mulVec (f u).ofLp) ∂μ :=
  ⟨physicalSobolevMatrixRowAmplitudeOperator R b hb hs hm hphys A hA hbound T,
    norm_physicalSobolevMatrixRowAmplitudeOperator_le R b hb hs hm hphys A hA hbound T,
    physicalSobolevMatrixRowAmplitudeOperator_ae_kernel_on_L1_core R b hb hc hs hm hphys A hA hbound T⟩

include hb hc hs hm hphys hA hbound in
/-- Original physical Sobolev rows bound a supplied native matrix channel
by its exact kernel, with no change of original operator
(`app:ch_osc:eq:amplitude-row`). -/
theorem norm_integralMatrixRowAmplitudeOperator_le_of_physicalSobolev
    (T : Lp ℂ 2 μ →L[ℂ] Output)
    (S : Lp (EuclideanSpace ℂ J) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ I) 2 (volume : Measure E))
    (K : E → X → ℂ)
    (hK : ∀ f : Lp (EuclideanSpace ℂ J) 2 μ, ∀ᵐ x ∂volume,
      Integrable (fun u ↦ K x u • f u) μ)
    (hT : ∀ g : Lp ℂ 2 μ, T g =ᵐ[volume] fun x ↦ ∫ u, K x u * g u ∂μ)
    (hS : ∀ f : Lp (EuclideanSpace ℂ J) 2 μ, S f =ᵐ[volume]
      fun x ↦ ∫ u, K x u • WithLp.toLp 2 ((b u x).mulVec (f u).ofLp) ∂μ) :
    ‖S‖ ≤ ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * rowAmplitudeConstant d R) * ‖T‖ * A := by
  have he : S = physicalSobolevMatrixRowAmplitudeOperator R b hb hs hm hphys A hA hbound T := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    exact (hS f).trans
      (physicalSobolevMatrixRowAmplitudeOperator_ae_kernel R b hb hc hs hm hphys A hA hbound T K hT f (hK f)).symm
  rw [he]
  exact norm_physicalSobolevMatrixRowAmplitudeOperator_le R b hb hs hm hphys A hA hbound T

end JanetCartan.AmplitudeBound.PaperEstimates
