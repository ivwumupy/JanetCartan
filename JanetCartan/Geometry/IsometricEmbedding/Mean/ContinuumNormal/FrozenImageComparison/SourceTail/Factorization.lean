module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.KernelBound
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.Freezing.VectorMultipliers
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.RealAssembly
/-!
# Exact mask factorization of the frozen Euclidean channel

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, the original measurement
and source masks factor around the bounded uncut constant-coefficient channel.
On supported L² inputs the measurement mask disappears from its adjoint.
The squared-energy difference is exactly the original source-square defect.
No differential operator is applied directly to arbitrary L² data.
-/

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ContDiff
open JanetCartan JanetCartan.PeriodicLocalL2 JanetCartan.ContinuumRow
open JanetCartan.ContinuumNormalReduction.ImageNormal
open JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ContinuumNormal.FrozenImageComparison
variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "C²" => Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure E)
local notation "R²" => EuclideanL2 n E
private theorem scalarMask_mul_const (μ : E → ℝ) (hμ : Continuous μ)
    (hμc : HasCompactSupport μ) (c : ℝ) :
    freezingPhysicalMultiplier (fun x ↦ μ x * c)
      (hμ.mul continuous_const) hμc.mul_right =
    (c : ℂ) • freezingPhysicalMultiplier μ hμ hμc := by
  ext1 f
  apply Lp.ext
  filter_upwards [freezingPhysicalMultiplier_coeFn (fun x ↦ μ x * c)
      (hμ.mul continuous_const) hμc.mul_right f,
    freezingPhysicalMultiplier_coeFn μ hμ hμc f,
    Lp.coeFn_smul (c : ℂ) (freezingPhysicalMultiplier μ hμ hμc f)] with x h₁ h₂ h₃
  change _ = ((c : ℂ) • freezingPhysicalMultiplier μ hμ hμc f) x
  rw [h₁, h₃, Pi.smul_apply, h₂]
  simp only [Complex.real_smul, Complex.ofReal_mul, smul_eq_mul]
  ring
private theorem block_factorization
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (χ μ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) (i j : Fin n) :
    euclideanChannelBlock (fun _ ↦ A) (fun _ ↦ 0) χ μ
      (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const)
      hχ hχc hμ hμc i j =
    (freezingPhysicalMultiplier μ hμ.continuous hμc).comp
      ((∑ a, (A a i j : ℂ) • imageDerivativeBesselL2Operator a).comp
        (freezingPhysicalMultiplier χ hχ.continuous hχc)) := by
  ext1 f
  simp only [euclideanChannelBlock, Matrix.zero_apply, ContinuousLinearMap.comp_apply,
    add_apply, sum_apply, smul_apply, map_sum, map_smul]
  rw [scalarMask_mul_const μ hμ.continuous hμc 0]
  simp only [Complex.ofReal_zero, smul_apply, zero_smul, add_zero]
  apply Finset.sum_congr rfl
  intro a _
  rw [scalarMask_mul_const μ hμ.continuous hμc (A a i j)]
  rfl
private theorem complex_factorization
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (χ μ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) :
    complexEuclideanChannel (fun _ ↦ A) (fun _ ↦ 0) χ μ
      (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const) hχ hχc hμ hμc =
    (freezingVectorPhysicalMultiplier μ hμ.continuous hμc).comp
      ((uncutComplexChannel A).comp (freezingVectorPhysicalMultiplier χ hχ.continuous hχc)) := by
  ext1 f
  apply (finiteL2CoordinateIsometry volume).injective
  ext i : 1
  simp only [complexEuclideanChannel, uncutComplexChannel, ContinuousLinearMap.comp_apply,
    finiteL2CoordinateIsometry_freezingVectorPhysicalMultiplier,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator, matrixOperator_apply,
    block_factorization, ContinuousLinearMap.comp_apply, map_sum]

private theorem inclusion_realCutoff (χ : E → ℝ) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (f : R²) :
    l2ComplexInclusion volume (realImageCutoffOperator χ hχ hχc f) =
      freezingVectorPhysicalMultiplier χ hχ hχc (l2ComplexInclusion volume f) := by
  apply Lp.ext
  filter_upwards [euclideanComplexInclusion.coeFn_compLpL
      (realImageCutoffOperator χ hχ hχc f),
    realImageCutoffOperator_coe χ hχ hχc f,
    freezingVectorPhysicalMultiplier_coeFn χ hχ hχc (l2ComplexInclusion volume f),
    euclideanComplexInclusion.coeFn_compLpL f] with x h₁ h₂ h₃ h₄
  change l2ComplexInclusion volume (realImageCutoffOperator χ hχ hχc f) x = _ at h₁
  change l2ComplexInclusion volume f x = _ at h₄
  rw [h₁, h₂, h₃, h₄, map_smul]

private theorem realPart_complexCutoff (χ : E → ℝ) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (f : C²) :
    l2RealPart volume (freezingVectorPhysicalMultiplier χ hχ hχc f) =
      realImageCutoffOperator χ hχ hχc (l2RealPart volume f) := by
  apply Lp.ext
  filter_upwards [euclideanRealPart.coeFn_compLpL
      (freezingVectorPhysicalMultiplier χ hχ hχc f),
    freezingVectorPhysicalMultiplier_coeFn χ hχ hχc f,
    realImageCutoffOperator_coe χ hχ hχc (l2RealPart volume f),
    euclideanRealPart.coeFn_compLpL f] with x h₁ h₂ h₃ h₄
  change l2RealPart volume (freezingVectorPhysicalMultiplier χ hχ hχc f) x = _ at h₁
  change l2RealPart volume f x = _ at h₄
  rw [h₁, h₂, h₃, h₄, map_smul]

/-- The original fixed physical mask acting on real Euclidean L², reused from
`realImageCutoffOperator` (`app:ch_background:prop:bg-frame`). -/
def fixedPhysicalMask (hR : 0 < R) (i : Fin 3) : R² →L[ℝ] R² :=
  realImageCutoffOperator (FixedCutoffs.physical hR i)
    (FixedCutoffs.physical hR i).continuous (FixedCutoffs.physical hR i).hasCompactSupport

/-- Exact factorization of the literal bounded masked channel as measurement
mask, uncut constant channel, and source mask. No cutoff is altered
(`app:ch_background:prop:bg-frame`). -/
theorem fixedEuclideanChannel_factorization (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    fixedEuclideanChannel hR A =
      (fixedPhysicalMask hR 1).comp ((uncutRealChannel A).comp (fixedPhysicalMask hR 2)) := by
  unfold fixedEuclideanChannel euclideanChannel
  rw [complex_factorization]
  ext1 u
  change l2RealPart volume
    (freezingVectorPhysicalMultiplier _ _ _
      (uncutComplexChannel A (freezingVectorPhysicalMultiplier _ _ _
        (l2ComplexInclusion volume u)))) = _
  rw [realPart_complexCutoff, ← inclusion_realCutoff]
  rfl

/-- Each original real physical mask is self-adjoint
(`app:ch_background:prop:bg-frame`). -/
theorem fixedPhysicalMask_adjoint (hR : 0 < R) (i : Fin 3) :
    (fixedPhysicalMask (n := n) hR i).adjoint = fixedPhysicalMask hR i :=
  realImageCutoffOperator_adjoint _ _ _

/-- The plateau of every original fixed physical mask fixes all L² fields
supported almost everywhere in the inner ball (`app:ch_background:prop:bg-frame`). -/
theorem fixedPhysicalMask_fixes_supported (hR : 0 < R) (i : Fin 3) (u : R²)
    (hu : ∀ᵐ x ∂volume, x ∉ ball (0 : E) R → u x = 0) :
    fixedPhysicalMask hR i u = u := by
  apply Lp.ext
  filter_upwards [realImageCutoffOperator_coe (FixedCutoffs.physical hR i)
    (FixedCutoffs.physical hR i).continuous
    (FixedCutoffs.physical hR i).hasCompactSupport u, hu] with x hx hu
  change fixedPhysicalMask hR i u x = _ at hx
  rw [hx]
  by_cases hs : x ∈ ball (0 : E) R
  · have hp : FixedCutoffs.physical hR i x = 1 := by
      apply interior_subset (FixedCutoffs.physical_plateau hR i _)
      apply closedBall_subset_closedBall _ (ball_subset_closedBall hs)
      have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
      nlinarith
    rw [hp, one_smul]
  · rw [hu hs, smul_zero]

/-- Remove the measurement mask from the literal Hilbert adjoint on every
supported L² input, retaining the original source mask
(`app:ch_background:prop:bg-frame`). -/
theorem fixedEuclideanChannel_adjoint_of_supported (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²)
    (hu : ∀ᵐ x ∂volume, x ∉ ball (0 : E) R → u x = 0) :
    (fixedEuclideanChannel hR A).adjoint u =
      fixedPhysicalMask hR 2 ((uncutRealChannel A).adjoint u) := by
  rw [fixedEuclideanChannel_factorization]
  simp only [ContinuousLinearMap.adjoint_comp, fixedPhysicalMask_adjoint,
    ContinuousLinearMap.comp_apply, fixedPhysicalMask_fixes_supported hR 1 u hu]
/-- The fixed real L² mask has its literal multiplication representative
(`app:ch_background:prop:bg-frame`). -/
theorem fixedPhysicalMask_coe (hR : 0 < R) (i : Fin 3) (u : R²) :
    fixedPhysicalMask hR i u =ᵐ[volume] fun x ↦ FixedCutoffs.physical hR i x • u x :=
  realImageCutoffOperator_coe _ _ _ _

private theorem norm_sq_eq_integral (v : R²) :
    ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private theorem integrable_norm_sq (v : R²) : Integrable (fun x ↦ ‖v x‖ ^ 2) := by
  simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) v v

private theorem fixedPhysicalMask_energy_defect_eq_integral (hR : 0 < R) (v : R²) :
    ‖v‖ ^ 2 - ‖fixedPhysicalMask hR 2 v‖ ^ 2 =
      ∫ x, (1 - fixedSourceSquare hR x) * ‖v x‖ ^ 2 := by
  calc
    _ = (∫ x, ‖v x‖ ^ 2) - ∫ x, ‖fixedPhysicalMask hR 2 v x‖ ^ 2 :=
      congrArg₂ (fun a b : ℝ ↦ a - b)
        (norm_sq_eq_integral v) (norm_sq_eq_integral (fixedPhysicalMask hR 2 v))
    _ = ∫ x, ‖v x‖ ^ 2 - ‖fixedPhysicalMask hR 2 v x‖ ^ 2 :=
      (integral_sub (integrable_norm_sq v) (integrable_norm_sq (fixedPhysicalMask hR 2 v))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [fixedPhysicalMask_coe hR 2 v] with x hx
      rw [hx, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      dsimp only [fixedSourceSquare]
      ring

/-- The literal normal energy difference is the defect of the original source
square. The source mask remains between the two adjoint factors; identifying
this integral with the separated double kernel is the remaining analytic step
(`app:ch_background:prop:bg-frame`). -/
theorem fixedEuclideanChannel_energy_defect_eq_integral (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²)
    (hu : ∀ᵐ x ∂volume, x ∉ ball (0 : E) R → u x = 0) :
    ‖(uncutRealChannel A).adjoint u‖ ^ 2 - ‖(fixedEuclideanChannel hR A).adjoint u‖ ^ 2 =
      ∫ x, (1 - fixedSourceSquare hR x) * ‖(uncutRealChannel A).adjoint u x‖ ^ 2 := by
  rw [fixedEuclideanChannel_adjoint_of_supported hR A u hu]
  exact fixedPhysicalMask_energy_defect_eq_integral hR ((uncutRealChannel A).adjoint u)
end JanetCartan.ContinuumNormal.FrozenImageComparison
