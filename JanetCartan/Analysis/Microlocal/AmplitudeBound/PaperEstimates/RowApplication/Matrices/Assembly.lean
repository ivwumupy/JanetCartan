module

public import JanetCartan.Analysis.Microlocal.NormalComparison.MatrixColumns

/-!
# The native matrix input for the original row kernels

The rectangular matrix statement in `app:ch_osc:lem:osc-amplitude` keeps
the arbitrary original source measure and the original scalar operator.
The already constructed scalar entries are assembled by the existing
finite matrix operator and the exact input/output coordinate isometries.
-/

@[expose] public noncomputable section

open MeasureTheory ContinuousLinearMap Filter

namespace JanetCartan.AmplitudeBound.PaperEstimates

open Pseudodifferential

variable {X Y I J : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype I] [Fintype J]

/-- Native vector L² assembly of the actual row entries, with their two
original measures (`app:ch_osc:lem:osc-amplitude`). -/
def nativeMatrixRowOperator (μ : Measure X) (ν : Measure Y)
    (B : I → J → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν) :
    Lp (EuclideanSpace ℂ J) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ I) 2 ν :=
  (finiteL2CoordinateIsometry (I := I) ν).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    matrixOperator B ∘L
      (finiteL2CoordinateIsometry (I := J) μ).toContinuousLinearEquiv.toContinuousLinearMap

/-- Exact coordinate action of the same original scalar entry operators
(`app:ch_osc:lem:osc-amplitude`). -/
theorem nativeMatrixRowOperator_coordinate (μ : Measure X) (ν : Measure Y)
    (B : I → J → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν)
    (f : Lp (EuclideanSpace ℂ J) 2 μ) (i : I) :
    finiteL2CoordinateIsometry ν (nativeMatrixRowOperator μ ν B f) i =
      ∑ j, B i j (finiteL2CoordinateIsometry μ f j) := by
  change (finiteL2CoordinateIsometry ν)
    ((finiteL2CoordinateIsometry ν).symm (matrixOperator B (finiteL2CoordinateIsometry μ f))) i = _
  rw [LinearIsometryEquiv.apply_symm_apply, matrixOperator_apply]

/-- Native coordinate conversion preserves the finite matrix operator norm
(`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_nativeMatrixRowOperator_eq (μ : Measure X) (ν : Measure Y)
    (B : I → J → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν) :
    ‖nativeMatrixRowOperator μ ν B‖ = ‖matrixOperator B‖ := by
  unfold nativeMatrixRowOperator
  rw [opNorm_linearIsometryEquiv_comp, opNorm_comp_linearIsometryEquiv]

/-- The fixed matrix size multiplies the original scalar row bound
(`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_nativeMatrixRowOperator_le_of_entry_bound (μ : Measure X) (ν : Measure Y)
    (B : I → J → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν) (C : ℝ) (hB : ∀ i j, ‖B i j‖ ≤ C) :
    ‖nativeMatrixRowOperator μ ν B‖ ≤ (Fintype.card I : ℝ) * (Fintype.card J : ℝ) * C := by
  rw [norm_nativeMatrixRowOperator_eq]
  exact norm_matrixOperator_le_of_entry_bound B C hB

/-- Scalar bounds for the original output coordinates imply the vector
row bound for the same supplied operator, with only the fixed square
root of its output dimension (`app:ch_osc:prop:osc-normal`). -/
theorem norm_rowVectorOperator_le_of_coordinate_bounds (μ : Measure X) (ν : Measure Y)
    (S : Lp ℂ 2 μ →L[ℂ] PiLp 2 (fun _ : I ↦ Lp ℂ 2 ν))
    {B : ℝ} (hB : 0 ≤ B)
    (hS : ∀ i, ‖(PiLp.proj (𝕜 := ℂ) 2 (fun _ : I ↦ Lp ℂ 2 ν) i).comp S‖ ≤ B) :
    ‖S‖ ≤ Real.sqrt (Fintype.card I : ℝ) * B := by
  let D : I → Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
    fun i ↦ ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : I ↦ Lp ℂ 2 ν) i).comp S).adjoint
  have he : S = (NormalPerturbation.weightedRow (fun _ : I ↦ 1) D).adjoint := by
    ext f i
    simp [NormalPerturbation.weightedRow_adjoint, NormalPerturbation.weightedColumn_apply, D]
  have hD (i : I) : ‖D i‖ ≤ B := by simpa only [D, LinearIsometryEquiv.norm_map] using hS i
  have hrow := NormalPerturbation.norm_weightedRow_le_of_bounds
    (fun _ : I ↦ 1) (fun _ ↦ zero_le_one) D hD
  rw [he, LinearIsometryEquiv.norm_map]
  simpa only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB] using hrow

/-- Integrability of the original native input passes to its scalar
coordinates. This is the actual L¹∩L² core used by the row kernels
(`app:ch_osc:eq:amplitude-row`). -/
theorem integrable_nativeRowCoordinate (μ : Measure X)
    (f : Lp (EuclideanSpace ℂ J) 2 μ) (hf : Integrable (f : X → EuclideanSpace ℂ J) μ)
    (j : J) : Integrable (finiteL2CoordinateIsometry μ f j : X → ℂ) μ := by
  apply (hf.eval_piLp j).congr
  exact (show finiteL2CoordinateIsometry μ f j =ᵐ[μ] fun u ↦ f u j from
    finiteL2Coordinates_apply_ae μ f j).symm

/-- An integrable original native kernel action supplies every scalar
coordinate action on the same L² class (`app:ch_osc:eq:amplitude-row`). -/
theorem integrable_nativeRowKernelCoordinate (μ : Measure X)
    (f : Lp (EuclideanSpace ℂ J) 2 μ) (K : X → ℂ)
    (hK : Integrable (fun u ↦ K u • f u) μ) (j : J) :
    Integrable (fun u ↦ K u * finiteL2CoordinateIsometry μ f j u) μ := by
  apply (hK.eval_piLp j).congr
  filter_upwards [finiteL2Coordinates_apply_ae μ f j] with u hu
  change finiteL2CoordinateIsometry μ f j u = f u j at hu
  simp only [PiLp.smul_apply, smul_eq_mul, hu]

end JanetCartan.AmplitudeBound.PaperEstimates
