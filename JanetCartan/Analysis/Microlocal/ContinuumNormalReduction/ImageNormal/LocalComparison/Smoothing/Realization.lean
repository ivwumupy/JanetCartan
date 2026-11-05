module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.Smoothing.Kernel
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.RemainderOperator
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector

/-!
# Bounded vector realization of the differentiated remainder kernel

For `app:ch_background:prop:bg-frame`, Step 1, every scalar entry of the
concrete differentiated remainder has a compact-kernel L² realization.
The existing finite-coordinate isometry assembles these entries on complex
vector L². The actual Hilbert adjoint reverses the spatial arguments and
transposes the component indices. Identification with the differential
composition and its H¹ estimate are separate obligations.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
open ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel Pseudodifferential
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- Real-kernel scalar realization used entrywise by the image-normal remainder
in `app:ch_background:prop:bg-frame`, Step 1. -/
def imageNormalRealKernelOperator (K : E × E → ℝ)
    (hc : Continuous K) (hs : HasCompactSupport K) : L² →L[ℂ] L² :=
  compactKernelOperator (μ := volume) (ν := volume)
    (t := fun x y ↦ (K (x, y) : ℂ))
    (Complex.continuous_ofReal.comp hc)
    (hs.comp_left (g := fun z : ℝ ↦ (z : ℂ)) rfl)

omit [Fintype I] [Fintype J] in
private theorem imageNormalRealKernelOperator_ae (K : E × E → ℝ)
    (hc : Continuous K) (hs : HasCompactSupport K) (f : L²) :
    imageNormalRealKernelOperator K hc hs f =ᵐ[volume] fun x ↦ ∫ y, (K (x, y) : ℂ) * f y :=
  compactKernelOperator_ae_integral _ _ f

omit [Fintype I] [Fintype J] in
private theorem imageNormalRealKernelOperator_adjoint_ae (K : E × E → ℝ)
    (hc : Continuous K) (hs : HasCompactSupport K) (f : L²) :
    (imageNormalRealKernelOperator K hc hs).adjoint f =ᵐ[volume]
      fun y ↦ ∫ x, (K (x, y) : ℂ) * f x := by
  simpa only [imageNormalRealKernelOperator, Complex.star_def, Complex.conj_ofReal] using
    compactKernelOperator_adjoint_ae_integral (μ := volume) (ν := volume)
      (t := fun x y ↦ (K (x, y) : ℂ)) (Complex.continuous_ofReal.comp hc)
      (hs.comp_left (g := fun z : ℝ ↦ (z : ℂ)) rfl) f

omit [Fintype I] [Fintype J] in
private theorem realCompactKernel_integrable (K : E × E → ℝ)
    (hc : Continuous K) (hs : HasCompactSupport K) (f : L²) (x : E) :
    Integrable (fun y ↦ (K (x, y) : ℂ) * f y) :=
  integrable_compactKernel_mul_L2 (t := fun x y ↦ (K (x, y) : ℂ))
    (Complex.continuous_ofReal.comp hc)
    (hs.comp_left (g := fun z : ℝ ↦ (z : ℂ)) rfl) f x

/-- Entrywise bounded realization of the actual differentiated remainder
in `app:ch_background:prop:bg-frame`, Step 1. No coefficient norm bound or
kernel estimate is assumed. -/
def localizedImageNormalRemainderEntryOperator
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ a, |y a| ≤ r)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) (i k : I) : L² →L[ℂ] L² :=
  imageNormalRealKernelOperator (localizedImageNormalRemainderKernel χ ψ A Z i k)
    (contDiff_localizedImageNormalRemainderKernel hr χ ψ hχ hψ hχs hψs A Z hA hZ i k).continuous
    (hasCompactSupport_localizedImageNormalRemainderKernel χ ψ hχs hψs A Z i k)

omit [Fintype I] in
/-- Absolute convergence of each differentiated remainder entry against
every scalar L² input (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integrable_localizedImageNormalRemainderEntry
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ a, |y a| ≤ r)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) (i k : I) (f : L²) (x : E) :
    Integrable (fun y ↦ (localizedImageNormalRemainderKernel χ ψ A Z i k (x, y) : ℂ) * f y) :=
  realCompactKernel_integrable (localizedImageNormalRemainderKernel χ ψ A Z i k)
    (contDiff_localizedImageNormalRemainderKernel hr χ ψ hχ hψ hχs hψs A Z hA hZ i k).continuous
    (hasCompactSupport_localizedImageNormalRemainderKernel χ ψ hχs hψs A Z i k) f x

omit [Fintype I] in
/-- Literal integral action of each entry on all of L²
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem localizedImageNormalRemainderEntryOperator_ae_integral
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ a, |y a| ≤ r)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) (i k : I) (f : L²) :
    localizedImageNormalRemainderEntryOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ i k f =ᵐ[volume]
      fun x ↦ ∫ y, (localizedImageNormalRemainderKernel χ ψ A Z i k (x, y) : ℂ) * f y :=
  imageNormalRealKernelOperator_ae _ _ _ f

omit [Fintype I] in
/-- The scalar adjoint uses the literal reversed differentiated kernel,
without a symmetry assumption (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem localizedImageNormalRemainderEntryOperator_adjoint_ae_integral
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ a, |y a| ≤ r)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) (i k : I) (f : L²) :
    (localizedImageNormalRemainderEntryOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ i k).adjoint f
      =ᵐ[volume] fun y ↦
        ∫ x, (localizedImageNormalRemainderKernel χ ψ A Z i k (x, y) : ℂ) * f x :=
  imageNormalRealKernelOperator_adjoint_ae _ _ _ f

/-- Bounded realization on the full complex vector L² space, using the
proved coordinate isometry (`app:ch_background:prop:bg-frame`, Step 1). -/
def localizedImageNormalRemainderOperator
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ a, |y a| ≤ r)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) :
    Lp (EuclideanSpace ℂ I) 2 (volume : Measure E) →L[ℂ]
      Lp (EuclideanSpace ℂ I) 2 (volume : Measure E) :=
  vectorMatrixL2Operator
    (localizedImageNormalRemainderEntryOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ)

/-- The vector adjoint transposes the actual scalar adjoint blocks
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem localizedImageNormalRemainderOperator_adjoint
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ a, |y a| ≤ r)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) :
    (localizedImageNormalRemainderOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ).adjoint =
      vectorMatrixL2Operator (fun k i ↦
        (localizedImageNormalRemainderEntryOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ i k).adjoint) :=
  vectorMatrixL2Operator_adjoint _

/-- The bounded vector realization integrates the explicit matrix entries
on every L² input (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem localizedImageNormalRemainderOperator_ae_integral
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ a, |y a| ≤ r)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (f : Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)) :
    localizedImageNormalRemainderOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦
        ∑ k, ∫ y, (localizedImageNormalRemainderKernel χ ψ A Z i k (x, y) : ℂ) * f y k) := by
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro i
  simp only [localizedImageNormalRemainderOperator,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator, AmplitudeBound.matrixOperator_apply]
  have he (k : I) := localizedImageNormalRemainderEntryOperator_ae_integral
    hr χ ψ hχ hψ hχs hψs A Z hA hZ i k (finiteL2CoordinateIsometry volume f k)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun k ↦ localizedImageNormalRemainderEntryOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ i k
      (finiteL2CoordinateIsometry volume f k)), ae_all_iff.mpr he] with x hx he
  simp only [Finset.sum_apply] at hx
  rw [hx]
  apply Finset.sum_congr rfl
  intro k _
  rw [he k]
  apply integral_congr_ae
  filter_upwards [finiteL2Coordinates_apply_ae volume f k] with y hy
  exact congrArg (fun z : ℂ ↦ (localizedImageNormalRemainderKernel χ ψ A Z i k (x, y) : ℂ) * z) hy

/-- The actual vector Hilbert adjoint has the reversed spatial kernel and
transposed component indices (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem localizedImageNormalRemainderOperator_adjoint_ae_integral
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ a, |y a| ≤ r)
    (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (f : Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)) :
    (localizedImageNormalRemainderOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ).adjoint f =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (fun k ↦
        ∑ i, ∫ x, (localizedImageNormalRemainderKernel χ ψ A Z i k (x, y) : ℂ) * f x i) := by
  rw [localizedImageNormalRemainderOperator_adjoint]
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro k
  simp only [finiteL2CoordinateIsometry_vectorMatrixL2Operator, AmplitudeBound.matrixOperator_apply]
  have he (i : I) := localizedImageNormalRemainderEntryOperator_adjoint_ae_integral
    hr χ ψ hχ hψ hχs hψs A Z hA hZ i k (finiteL2CoordinateIsometry volume f i)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i ↦ (localizedImageNormalRemainderEntryOperator hr χ ψ hχ hψ hχs hψs A Z hA hZ i k).adjoint
      (finiteL2CoordinateIsometry volume f i)), ae_all_iff.mpr he] with y hy he
  simp only [Finset.sum_apply] at hy
  rw [hy]
  apply Finset.sum_congr rfl
  intro i _
  rw [he i]
  apply integral_congr_ae
  filter_upwards [finiteL2Coordinates_apply_ae volume f i] with x hx
  exact congrArg (fun z : ℂ ↦ (localizedImageNormalRemainderKernel χ ψ A Z i k (x, y) : ℂ) * z) hx

end JanetCartan.ContinuumNormalReduction.ImageNormal
