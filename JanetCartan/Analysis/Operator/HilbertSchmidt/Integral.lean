module

public import JanetCartan.Analysis.Operator.HilbertSchmidt.Trace
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Convex.Integral
/-!
# Traces of averaged positive normals

The Tonelli step in `app:ch_waves:thm:sampling`. The average here is the actual
Bochner integral of the operator family. Operator integrability and integrability
of its positive trace are explicit analytic inputs.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory

namespace JanetCartan

variable {𝕜 E ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- A diagonal coefficient as a continuous real linear functional
(`app:ch_waves:thm:sampling`). -/
def diagonalCLM (y : E) : (E →L[𝕜] E) →L[ℝ] ℝ :=
  RCLike.reCLM ∘L (((innerSL 𝕜 y) ∘L (ContinuousLinearMap.apply 𝕜 E y)).restrictScalars ℝ)

omit [CompleteSpace E] in
/-- Evaluation of the diagonal functional
(`app:ch_waves:thm:sampling`). -/
theorem diagonalCLM_apply (y : E) (A : E →L[𝕜] E) :
    diagonalCLM y A = RCLike.re (inner 𝕜 y (A y)) := rfl

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}

/-- Summability and value of the diagonal of an averaged positive operator
(`app:ch_waves:thm:sampling`). -/
theorem hasSum_diagonal_integral [Countable ι] (b : HilbertBasis ι 𝕜 E)
    (A : Z → E →L[𝕜] E) (hA : Integrable A μ)
    (hpos : ∀ z y, 0 ≤ RCLike.re (inner 𝕜 y (A z y)))
    (hs : ∀ z, Summable (fun i ↦ RCLike.re (inner 𝕜 (b i) (A z (b i)))))
    (hint : Integrable (fun z ↦ positiveTrace b (A z)) μ) :
    HasSum (fun i ↦ RCLike.re (inner 𝕜 (b i) ((∫ z, A z ∂μ) (b i))))
      (∫ z, positiveTrace b (A z) ∂μ) := by
  have hh : HasSum (fun i ↦ ∫ z, RCLike.re (inner 𝕜 (b i) (A z (b i))) ∂μ)
      (∫ z, positiveTrace b (A z) ∂μ) := by
    apply hasSum_integral_of_dominated_convergence
      (fun i z ↦ RCLike.re (inner 𝕜 (b i) (A z (b i))))
    · intro i
      exact ((diagonalCLM (b i)).integrable_comp hA).aestronglyMeasurable
    · intro i
      exact Filter.Eventually.of_forall (fun z ↦ by simp [Real.norm_eq_abs, abs_of_nonneg (hpos z (b i))])
    · exact Filter.Eventually.of_forall hs
    · exact hint
    · exact Filter.Eventually.of_forall (fun z ↦ (hs z).hasSum)
  convert hh using 1
  ext i
  exact ((diagonalCLM (b i)).integral_comp_comm hA).symm

/-- Interchange of positive trace and operator integration
(`app:ch_waves:thm:sampling`). -/
theorem positiveTrace_integral [Countable ι] (b : HilbertBasis ι 𝕜 E)
    (A : Z → E →L[𝕜] E) (hA : Integrable A μ)
    (hpos : ∀ z y, 0 ≤ RCLike.re (inner 𝕜 y (A z y)))
    (hs : ∀ z, Summable (fun i ↦ RCLike.re (inner 𝕜 (b i) (A z (b i)))))
    (hint : Integrable (fun z ↦ positiveTrace b (A z)) μ) :
    positiveTrace b (∫ z, A z ∂μ) = ∫ z, positiveTrace b (A z) ∂μ :=
  (hasSum_diagonal_integral b A hA hpos hs hint).tsum_eq

end JanetCartan

namespace JanetCartan

variable {𝕜 E F ι κ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
  {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}

/-- The trace of an averaged weighted normal is the integral of the weighted
squared Hilbert–Schmidt norms
(`app:ch_waves:thm:sampling`). -/
theorem positiveTrace_integral_weighted_normal [Countable κ]
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (T : Z → E →L[𝕜] F) (w : Z → ℝ)
    (hT : ∀ z, IsHilbertSchmidt b (T z)) (hw : ∀ z, 0 ≤ w z)
    (hA : Integrable (fun z ↦ w z • (T z ∘L (T z).adjoint)) μ)
    (hint : Integrable (fun z ↦ w z * hilbertSchmidtSq b (T z)) μ) :
    positiveTrace c (∫ z, w z • (T z ∘L (T z).adjoint) ∂μ) =
      ∫ z, w z * hilbertSchmidtSq b (T z) ∂μ := by
  have hd (z : Z) (y : F) :
      RCLike.re (inner 𝕜 y ((w z • (T z ∘L (T z).adjoint)) y)) =
        w z * ‖(T z).adjoint y‖ ^ 2 := by
    have hh := (diagonalCLM (𝕜 := 𝕜) y).map_smul (w z) (T z ∘L (T z).adjoint)
    simpa only [diagonalCLM_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ← (T z).adjoint_inner_left, inner_self_eq_norm_sq_to_K,
      ← RCLike.ofReal_pow, RCLike.ofReal_re] using hh
  have heq (z : Z) : positiveTrace c (w z • (T z ∘L (T z).adjoint)) =
      w z * hilbertSchmidtSq b (T z) := by
    simp only [positiveTrace, hd, tsum_mul_left]
    exact congrArg (fun r ↦ w z * r) (isHilbertSchmidt_adjoint b c (T z) (hT z)).2
  rw [positiveTrace_integral c _ hA]
  · simp only [heq]
  · intro z y
    rw [hd]
    exact mul_nonneg (hw z) (sq_nonneg _)
  · intro z
    simpa only [hd] using (isHilbertSchmidt_adjoint b c (T z) (hT z)).1.mul_left (w z)
  · simpa only [heq] using hint
end JanetCartan

namespace JanetCartan

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
  {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} [IsProbabilityMeasure μ]

omit [CompleteSpace E] in
/-- Expectations of compact operators remain compact, as used for centered blocks
in `app:ch_waves:thm:sampling`. -/
theorem isCompactOperator_integral (A : Z → E →L[𝕜] F) (hA : Integrable A μ)
    (hc : ∀ᵐ z ∂μ, IsCompactOperator (A z)) : IsCompactOperator (∫ z, A z ∂μ : E →L[𝕜] F) := by
  let S := (compactOperator (RingHom.id 𝕜) E F).restrictScalars ℝ
  exact S.convex.integral_mem isClosed_setOfPred_isCompactOperator hc hA
end JanetCartan
