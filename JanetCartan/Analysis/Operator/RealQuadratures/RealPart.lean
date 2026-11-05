module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Real part and complex inclusion on Euclidean-valued L² spaces

The concrete real-output maps in `app:ch_osc:cor:osc-real`. Finite coordinate sets
carry the Euclidean norm (hence the Frobenius norm when coordinates index matrices).
Mathlib's complex inner product is conjugate-linear in its first argument; taking
its real part gives the real Hilbert inner product used in the manuscript.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace JanetCartan

variable {ι : Type*} [Fintype ι]

/-- Componentwise real part, as used in `app:ch_osc:cor:osc-real`. -/
def euclideanRealPart : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℝ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z ↦ WithLp.toLp 2 (fun i ↦ (z i).re)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }

/-- The real-output inclusion into the complex space in `app:ch_osc:eq:osc-factor-four`. -/
def euclideanComplexInclusion : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ WithLp.toLp 2 (fun i ↦ (x i : ℂ))
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }

/-- The real-part map acts componentwise (`app:ch_osc:cor:osc-real`). -/
@[simp] theorem euclideanRealPart_apply (z : EuclideanSpace ℂ ι) (i : ι) :
    euclideanRealPart z i = (z i).re := rfl

/-- The inclusion acts componentwise (`app:ch_osc:cor:osc-real`). -/
@[simp] theorem euclideanComplexInclusion_apply (x : EuclideanSpace ℝ ι) (i : ι) :
    euclideanComplexInclusion x i = (x i : ℂ) := rfl

/-- The real-part/inclusion pairing in the proof of `app:ch_osc:cor:osc-real`. -/
theorem euclideanRealPart_inner (z : EuclideanSpace ℂ ι) (x : EuclideanSpace ℝ ι) :
    ⟪euclideanRealPart z, x⟫_ℝ = ⟪z, euclideanComplexInclusion x⟫_ℝ := by
  simp [PiLp.inner_apply, Complex.inner, RCLike.inner_apply, mul_comm]

/-- Real inclusion preserves the Euclidean norm (`app:ch_osc:cor:osc-real`). -/
theorem euclideanComplexInclusion_norm (x : EuclideanSpace ℝ ι) :
    ‖euclideanComplexInclusion x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq]

/-- The actual real Hilbert adjoint of real part (`app:ch_osc:cor:osc-real`). -/
theorem euclideanRealPart_adjoint :
    (euclideanRealPart (ι := ι)).adjoint = euclideanComplexInclusion := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x z
  rw [real_inner_comm, ← euclideanRealPart_inner, real_inner_comm]

/-- The inclusion is a contraction (`app:ch_osc:cor:osc-real`). -/
theorem euclideanComplexInclusion_norm_le :
    ‖euclideanComplexInclusion (ι := ι)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [euclideanComplexInclusion_norm, one_mul, le_refl]

/-- Real part is a contraction (`app:ch_osc:cor:osc-real`). -/
theorem euclideanRealPart_norm_le : ‖euclideanRealPart (ι := ι)‖ ≤ 1 := by
  rw [← ContinuousLinearMap.adjoint.norm_map, euclideanRealPart_adjoint]
  exact euclideanComplexInclusion_norm_le

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- Pointwise real part on the full L² space in `app:ch_osc:cor:osc-real`. -/
def l2RealPart : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 μ :=
  euclideanRealPart.compLpL 2 μ

/-- Pointwise inclusion of real L² outputs in `app:ch_osc:eq:osc-factor-four`. -/
def l2ComplexInclusion : Lp (EuclideanSpace ℝ ι) 2 μ →L[ℝ] Lp (EuclideanSpace ℂ ι) 2 μ :=
  euclideanComplexInclusion.compLpL 2 μ

/-- The L² real-part/inclusion pairing (`app:ch_osc:cor:osc-real`). -/
theorem l2RealPart_inner (z : Lp (EuclideanSpace ℂ ι) 2 μ)
    (x : Lp (EuclideanSpace ℝ ι) 2 μ) :
    ⟪l2RealPart μ z, x⟫_ℝ = ⟪z, l2ComplexInclusion μ x⟫_ℝ := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(euclideanRealPart (ι := ι)).coeFn_compLpL z,
    (euclideanComplexInclusion (ι := ι)).coeFn_compLpL x] with a hz hx
  simpa only [l2RealPart, l2ComplexInclusion, hz, hx] using
    euclideanRealPart_inner (z a) (x a)

/-- The real adjoint of L² real part is inclusion (`app:ch_osc:cor:osc-real`). -/
theorem l2RealPart_adjoint : (l2RealPart (ι := ι) μ).adjoint = l2ComplexInclusion μ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x z
  rw [real_inner_comm, ← l2RealPart_inner, real_inner_comm]

/-- The L² real-part map is a contraction (`app:ch_osc:cor:osc-real`). -/
theorem l2RealPart_norm_le : ‖l2RealPart (ι := ι) μ‖ ≤ 1 :=
  ((euclideanRealPart (ι := ι)).norm_compLpL_le (p := 2) (μ := μ)).trans euclideanRealPart_norm_le

/-- Real L² inclusion is a contraction (`app:ch_osc:cor:osc-real`). -/
theorem l2ComplexInclusion_norm_le : ‖l2ComplexInclusion (ι := ι) μ‖ ≤ 1 :=
  ((euclideanComplexInclusion (ι := ι)).norm_compLpL_le (p := 2) (μ := μ)).trans
    euclideanComplexInclusion_norm_le

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [InnerProductSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace E] [CompleteSpace F]

omit [IsScalarTower ℝ ℂ E] [CompleteSpace E] in
/-- Real and complex inner products agree after taking real part
(`app:ch_osc:cor:osc-real`), even when their instances are not definitionally equal. -/
theorem real_inner_eq_complex_re (x y : E) : ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  exact (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
    (𝕜 := ℂ) x y).symm

/-- Restricting a complex operator to real scalars preserves its conjugate adjoint
(`app:ch_osc:cor:osc-real`); it does not replace it with a complex transpose. -/
theorem adjoint_restrictScalars_complex (T : E →L[ℂ] F) :
    (T.restrictScalars ℝ).adjoint = T.adjoint.restrictScalars ℝ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro y x
  simp only [ContinuousLinearMap.coe_restrictScalars', real_inner_eq_complex_re,
    ContinuousLinearMap.adjoint_inner_left]

end JanetCartan
