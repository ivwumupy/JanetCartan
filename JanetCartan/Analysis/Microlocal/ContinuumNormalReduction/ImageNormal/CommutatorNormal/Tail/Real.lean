module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.Tail.Realization
public import JanetCartan.Analysis.Operator.RealQuadratures
/-!
# Real realization of the actual intermediate-localization tail

For `app:ch_background:prop:bg-frame`, Step 1, the proved matrix kernel is real.
Compression to real vector L² therefore commutes with complex inclusion, for
both the tail and its literal Hilbert adjoint. The complex H¹ estimates carry
over with the same constant.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff SchwartzMap
open JanetCartan.Pseudodifferential
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "C²" => Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)
local notation "R²" => Lp (EuclideanSpace ℝ I) 2 (volume : Measure E)

private theorem realCompression_adjoint (T : C² →L[ℂ] C²) :
    (realOutputCompression T).adjoint = realOutputCompression (T).adjoint := by
  have hi : (l2ComplexInclusion (ι := I) (volume : Measure E)).adjoint = l2RealPart volume := by
    rw [← l2RealPart_adjoint, ContinuousLinearMap.adjoint_adjoint]
  simp only [realOutputCompression, ContinuousLinearMap.adjoint_comp,
    adjoint_restrictScalars_complex, l2RealPart_adjoint, hi, ContinuousLinearMap.comp_assoc]

private theorem realMatrixIntegral_inclusion
    (K : I → I → E × E → ℝ) (f : R²) (x : E) (i : I) :
    (∑ k, ∫ y, (K i k (x, y) : ℂ) * l2ComplexInclusion volume f y k) =
      ((∑ k, ∫ y, K i k (x, y) * f y k : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [euclideanComplexInclusion.coeFn_compLpL f] with y hy
  change l2ComplexInclusion volume f y = euclideanComplexInclusion (f y) at hy
  simp only [hy, euclideanComplexInclusion_apply, Complex.ofReal_mul]

private theorem realCompression_ae_integral
    (T : C² →L[ℂ] C²) (K : I → I → E × E → ℝ)
    (hT : ∀ f : C², T f =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ ∑ k, ∫ y, (K i k (x, y) : ℂ) * f y k)) (f : R²) :
    realOutputCompression T f =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ ∑ k, ∫ y, K i k (x, y) * f y k) := by
  filter_upwards [euclideanRealPart.coeFn_compLpL (T (l2ComplexInclusion volume f)),
    hT (l2ComplexInclusion volume f)] with x hx hT
  change realOutputCompression T f x = euclideanRealPart _ at hx
  rw [hx, hT]
  ext i
  change (∑ k, ∫ y, (K i k (x, y) : ℂ) * l2ComplexInclusion volume f y k).re = _
  rw [realMatrixIntegral_inclusion]
  rfl

private theorem inclusion_realCompression
    (T : C² →L[ℂ] C²) (K : I → I → E × E → ℝ)
    (hT : ∀ f : C², T f =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ ∑ k, ∫ y, (K i k (x, y) : ℂ) * f y k)) (f : R²) :
    l2ComplexInclusion volume (realOutputCompression T f) = T (l2ComplexInclusion volume f) := by
  apply Lp.ext
  filter_upwards [euclideanComplexInclusion.coeFn_compLpL (realOutputCompression T f),
    realCompression_ae_integral T K hT f, hT (l2ComplexInclusion volume f)] with x hx hy hz
  change l2ComplexInclusion volume (realOutputCompression T f) x = euclideanComplexInclusion _ at hx
  rw [hx, hy, hz]
  ext i
  exact (realMatrixIntegral_inclusion K f x i).symm


/-- The actual tail on real vector Lebesgue L²
(`app:ch_background:prop:bg-frame`, Step 1). -/
def realCoefficientSourceCommutatorTailOperator (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1) : R² →L[ℝ] R² :=
  realOutputCompression (coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau)

/-- The real Hilbert adjoint is the compression of the complex Hilbert
adjoint (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realCoefficientSourceCommutatorTailOperator_adjoint (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1) :
    (realCoefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau).adjoint = realOutputCompression (coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau).adjoint := realCompression_adjoint (coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau)

/-- Literal real matrix-kernel action on every real L² input
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realCoefficientSourceCommutatorTailOperator_ae_integral (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1) (f : R²) :
    (realCoefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) f =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ ∑ k, ∫ y, (coefficientSourceCommutatorTailKernel A Z χ μ β) i k (x, y) * f y k) :=
  realCompression_ae_integral (coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) (coefficientSourceCommutatorTailKernel A Z χ μ β)
    (coefficientSourceCommutatorTailOperator_ae_integral A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) f

/-- Literal real adjoint action with transposed indices and reversed
spatial variables (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realCoefficientSourceCommutatorTailOperator_adjoint_ae_integral (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1) (f : R²) :
    (realCoefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau).adjoint f =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (fun k ↦ ∑ i, ∫ x, (coefficientSourceCommutatorTailKernel A Z χ μ β) i k (x, y) * f x i) := by
  rw [realCoefficientSourceCommutatorTailOperator_adjoint]
  exact realCompression_ae_integral (coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau).adjoint (fun k i p ↦ (coefficientSourceCommutatorTailKernel A Z χ μ β) i k p.swap)
    (coefficientSourceCommutatorTailOperator_adjoint_ae_integral A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) f

/-- Complex inclusion intertwines the actual real and complex tails,
by the proved real kernel (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem l2ComplexInclusion_realCoefficientSourceCommutatorTailOperator (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1) (f : R²) :
    l2ComplexInclusion volume ((realCoefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) f) = (coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) (l2ComplexInclusion volume f) :=
  inclusion_realCompression (coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) (coefficientSourceCommutatorTailKernel A Z χ μ β)
    (coefficientSourceCommutatorTailOperator_ae_integral A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) f

/-- Complex inclusion also intertwines the literal real and complex
Hilbert adjoints (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem l2ComplexInclusion_realCoefficientSourceCommutatorTailOperator_adjoint (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1) (f : R²) :
    l2ComplexInclusion volume ((realCoefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau).adjoint f) = (coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau).adjoint (l2ComplexInclusion volume f) := by
  rw [realCoefficientSourceCommutatorTailOperator_adjoint]
  exact inclusion_realCompression (coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau).adjoint (fun k i p ↦ (coefficientSourceCommutatorTailKernel A Z χ μ β) i k p.swap)
    (coefficientSourceCommutatorTailOperator_adjoint_ae_integral A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) f

/-- Both real L²-to-H¹ endpoints, with exactly the complex endpoint
constant (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realCoefficientSourceCommutatorTailOperator_sobolev_one_bounds (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : R²,
      MemVectorFourierSobolev 1 (l2ComplexInclusion volume ((realCoefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) f)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume ((realCoefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) f)) ≤ C * ‖f‖ ∧
      MemVectorFourierSobolev 1 (l2ComplexInclusion volume ((realCoefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau).adjoint f)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume ((realCoefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau).adjoint f)) ≤ C * ‖f‖ := by
  obtain ⟨C, hC, hT⟩ := coefficientSourceCommutatorTailOperator_sobolev_one_bounds A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau
  refine ⟨C, hC, fun f ↦ ?_⟩
  rw [l2ComplexInclusion_realCoefficientSourceCommutatorTailOperator,
    l2ComplexInclusion_realCoefficientSourceCommutatorTailOperator_adjoint]
  have hb : ‖l2ComplexInclusion volume f‖ ≤ ‖f‖ := by
    simpa using (l2ComplexInclusion volume).le_of_opNorm_le (l2ComplexInclusion_norm_le volume) f
  exact ⟨(hT _).1, (hT _).2.1.trans (mul_le_mul_of_nonneg_left hb hC),
    (hT _).2.2.1, (hT _).2.2.2.trans (mul_le_mul_of_nonneg_left hb hC)⟩

end JanetCartan.ContinuumNormalReduction.ImageNormal
