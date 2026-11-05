module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.Tail.MatrixKernel
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.Smoothing.ScalarSobolev

/-!
# Bounded vector realization of the actual localization tail

For `app:ch_background:prop:bg-frame`, Step 1, realize the proved smooth compact
matrix kernel on Euclidean Lebesgue L². Its literal Hilbert adjoint reverses the
spatial arguments and transposes the matrix indices. The Schwartz action is
identified with the original untruncated tail, and both H¹ endpoints follow
from the proved compact-kernel estimates.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff SchwartzMap
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
open ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel Pseudodifferential
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)
local notation "V²" => Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)
local notation "S" => 𝓢(E, ℂ)



/-- Scalar blocks of the bounded localization tail, constructed from its
actual differentiated kernel (`app:ch_background:prop:bg-frame`, Step 1). -/
def coefficientSourceCommutatorTailEntryOperator
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)

    (i k : I) : L² →L[ℂ] L² :=
  imageNormalRealKernelOperator ((coefficientSourceCommutatorTailKernel A Z χ μ β) i k) ((contDiff_coefficientSourceCommutatorTailKernel A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k).continuous ((hasCompactSupport_coefficientSourceCommutatorTailKernel A Z χ μ β hχc hβc) i k)


omit [Fintype I] in
/-- The scalar blocks integrate the literal matrix entries
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientSourceCommutatorTailEntryOperator_ae_integral
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)

    (i k : I) (f : L²) :
    (coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k f =ᵐ[volume] fun x ↦ ∫ y, ((coefficientSourceCommutatorTailKernel A Z χ μ β) i k (x, y) : ℂ) * f y :=
  compactKernelOperator_ae_integral _ _ f

omit [Fintype I] in
/-- The scalar Hilbert adjoint reverses the real kernel
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientSourceCommutatorTailEntryOperator_adjoint_ae_integral
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)

    (i k : I) (f : L²) :
    ((coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k).adjoint f =ᵐ[volume] fun y ↦ ∫ x, ((coefficientSourceCommutatorTailKernel A Z χ μ β) i k (x, y) : ℂ) * f x := by
  simpa only [coefficientSourceCommutatorTailEntryOperator, imageNormalRealKernelOperator,
    Complex.star_def, Complex.conj_ofReal] using
    compactKernelOperator_adjoint_ae_integral (μ := volume) (ν := volume)
      (t := fun x y ↦ ((coefficientSourceCommutatorTailKernel A Z χ μ β) i k (x, y) : ℂ))
      (Complex.continuous_ofReal.comp ((contDiff_coefficientSourceCommutatorTailKernel A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k).continuous)
      (((hasCompactSupport_coefficientSourceCommutatorTailKernel A Z χ μ β hχc hβc) i k).comp_left (g := fun z : ℝ ↦ (z : ℂ)) rfl) f

/-- The actual localization tail on complex vector Lebesgue L²
(`app:ch_background:prop:bg-frame`, Step 1). -/
def coefficientSourceCommutatorTailOperator
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)

    : V² →L[ℂ] V² := vectorMatrixL2Operator (coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau)

/-- The literal vector Hilbert adjoint transposes the actual adjoint blocks
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientSourceCommutatorTailOperator_adjoint
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)

    :
    ((coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau)).adjoint = vectorMatrixL2Operator (fun k i ↦ ((coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k).adjoint) :=
  vectorMatrixL2Operator_adjoint _

/-- The bounded vector operator integrates the concrete matrix kernel on
all L² inputs (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientSourceCommutatorTailOperator_ae_integral
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)

    (f : V²) :
    (coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) f =ᵐ[volume] fun x ↦ WithLp.toLp 2 (fun i ↦
      ∑ k, ∫ y, ((coefficientSourceCommutatorTailKernel A Z χ μ β) i k (x, y) : ℂ) * f y k) := by
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro i
  simp only [coefficientSourceCommutatorTailOperator,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator, AmplitudeBound.matrixOperator_apply]
  have he (k : I) := coefficientSourceCommutatorTailEntryOperator_ae_integral
    A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau i k (finiteL2CoordinateIsometry volume f k)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun k ↦ (coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k (finiteL2CoordinateIsometry volume f k)), ae_all_iff.mpr he] with x hx he
  simp only [Finset.sum_apply] at hx
  rw [hx]
  apply Finset.sum_congr rfl
  intro k _
  rw [he k]
  apply integral_congr_ae
  filter_upwards [finiteL2Coordinates_apply_ae volume f k] with y hy
  exact congrArg (fun z : ℂ ↦ ((coefficientSourceCommutatorTailKernel A Z χ μ β) i k (x, y) : ℂ) * z) hy

/-- The literal adjoint integrates the reversed matrix kernel, with all
zeroth-order terms retained (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientSourceCommutatorTailOperator_adjoint_ae_integral
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)

    (f : V²) :
    ((coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau)).adjoint f =ᵐ[volume] fun y ↦ WithLp.toLp 2 (fun k ↦
      ∑ i, ∫ x, ((coefficientSourceCommutatorTailKernel A Z χ μ β) i k (x, y) : ℂ) * f x i) := by
  rw [coefficientSourceCommutatorTailOperator_adjoint]
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro k
  simp only [finiteL2CoordinateIsometry_vectorMatrixL2Operator, AmplitudeBound.matrixOperator_apply]
  have he (i : I) := coefficientSourceCommutatorTailEntryOperator_adjoint_ae_integral
    A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau i k (finiteL2CoordinateIsometry volume f i)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i ↦ ((coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k).adjoint (finiteL2CoordinateIsometry volume f i)), ae_all_iff.mpr he] with y hy he
  simp only [Finset.sum_apply] at hy
  rw [hy]
  apply Finset.sum_congr rfl
  intro i _
  rw [he i]
  apply integral_congr_ae
  filter_upwards [finiteL2Coordinates_apply_ae volume f i] with x hx
  exact congrArg (fun z : ℂ ↦ ((coefficientSourceCommutatorTailKernel A Z χ μ β) i k (x, y) : ℂ) * z) hx

/-- The bounded realization agrees with the exact published Schwartz tail,
for every Schwartz family and its vector L² representative
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientSourceCommutatorTailOperator_ae_schwartz
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)

   
    (hμc : HasCompactSupport μ) (hβμ : ∀ y ∈ tsupport μ, β y = 1)
    (v : I → S) (f : V²) (hf : f =ᵐ[volume] fun x ↦ WithLp.toLp 2 (fun i ↦ v i x)) :
    (coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) f =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ coefficientSourceCommutatorTailSchwartz A Z χ μ β v i x) := by
  filter_upwards [coefficientSourceCommutatorTailOperator_ae_integral
    A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau f] with x hx
  rw [hx]
  ext i
  change (∑ k, ∫ y, (coefficientSourceCommutatorTailKernel A Z χ μ β i k (x, y) : ℂ) * f y k) =
    coefficientSourceCommutatorTailSchwartz A Z χ μ β v i x
  rw [coefficientSourceCommutatorTailSchwartz_eq_integral
    A Z χ μ β hA hZ hχ hχc hμ hμc hβ hβc hδ hplateau hβμ v x i]
  apply Finset.sum_congr rfl
  intro k _
  apply integral_congr_ae
  filter_upwards [hf] with y hy
  rw [hy]

/-- Both the actual localization tail and its literal Hilbert adjoint map
L² to H¹. Every analytic input is supplied by the explicit matrix kernel
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem coefficientSourceCommutatorTailOperator_sobolev_one_bounds
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ) (χ μ β : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hμ : ContDiff ℝ ∞ μ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)

    :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : V²,
      MemVectorFourierSobolev 1 ((coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) f) ∧ vectorFourierSobolevNorm 1 ((coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) f) ≤ C * ‖f‖ ∧
      MemVectorFourierSobolev 1 (((coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau)).adjoint f) ∧
        vectorFourierSobolevNorm 1 (((coefficientSourceCommutatorTailOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau)).adjoint f) ≤ C * ‖f‖ := by
  classical
  have hentry (i k : I) : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : L²,
      MemFourierSobolev 1 ((coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k f) ∧ fourierSobolevNorm 1 ((coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k f) ≤ C * ‖f‖ ∧
      MemFourierSobolev 1 (((coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k).adjoint f) ∧
        fourierSobolevNorm 1 (((coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k).adjoint f) ≤ C * ‖f‖ :=
    imageNormalRealKernelOperator_sobolev_one_bounds ((coefficientSourceCommutatorTailKernel A Z χ μ β) i k) ((contDiff_coefficientSourceCommutatorTailKernel A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k) ((hasCompactSupport_coefficientSourceCommutatorTailKernel A Z χ μ β hχc hβc) i k)
  choose C hC hentry using hentry
  let D : ℝ := ∑ i, ∑ k, C i k
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun k _ ↦ hC i k
  have hCD (i k : I) : C i k ≤ D :=
    (Finset.single_le_sum (fun j _ ↦ hC i j) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (fun j _ ↦ Finset.sum_nonneg fun l _ ↦ hC j l) (Finset.mem_univ i))
  have hforward : ∀ i k f, MemFourierSobolev 0 f →
      MemFourierSobolev 1 ((coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k f) ∧
        fourierSobolevNorm 1 ((coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k f) ≤ D * (fourierSobolevNorm 0 f + 0 * ‖f‖) := by
    intro i k f _
    exact ⟨(hentry i k f).1, by
      simpa only [fourierSobolevNorm_zero, zero_mul, add_zero] using
        (hentry i k f).2.1.trans (mul_le_mul_of_nonneg_right (hCD i k) (norm_nonneg f))⟩
  have hreverse : ∀ k i f, MemFourierSobolev 0 f →
      MemFourierSobolev 1 (((coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k).adjoint f) ∧
        fourierSobolevNorm 1 (((coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k).adjoint f) ≤ D * (fourierSobolevNorm 0 f + 0 * ‖f‖) := by
    intro k i f _
    exact ⟨(hentry i k f).2.2.1, by
      simpa only [fourierSobolevNorm_zero, zero_mul, add_zero] using
        (hentry i k f).2.2.2.trans (mul_le_mul_of_nonneg_right (hCD i k) (norm_nonneg f))⟩
  refine ⟨(Fintype.card I : ℝ) * (Fintype.card I : ℝ) * D, by positivity, fun f ↦ ?_⟩
  have hf : MemVectorFourierSobolev 0 f := fun _ ↦ memFourierSobolev_zero _
  have hF := vectorMatrixL2Operator_fourierSobolev_bound (coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) 0 1 D 0 hD le_rfl hforward f hf
  have hR := vectorMatrixL2Operator_fourierSobolev_bound
    (fun k i ↦ ((coefficientSourceCommutatorTailEntryOperator A Z χ μ β hA hZ hχ hχc hμ hβ hβc hδ hplateau) i k).adjoint) 0 1 D 0 hD le_rfl hreverse f hf
  rw [coefficientSourceCommutatorTailOperator_adjoint]
  simpa only [coefficientSourceCommutatorTailOperator,
    vectorFourierSobolevNorm_zero, zero_mul, add_zero] using
    And.intro hF.1 (And.intro hF.2 hR)

end JanetCartan.ContinuumNormalReduction.ImageNormal
