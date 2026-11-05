module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FullNormalKernel.Coefficients
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FullNormalKernel.Integrability

/-!
# Full normal amplitude kernels

The normal series of `app:ch_osc:lem:osc-amplitude` and
`app:ch_osc:eq:two-position-normal-bound` in `paper.tex` equals the literal
integral kernel and satisfies the claimed L² estimate. The genuine input
kernel identity determines the actual adjoint; compact joint support supplies
integrability for Fourier summation and Fubini without finite measure of `D`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff

namespace JanetCartan.AmplitudeBound

variable {d m : ℕ}

variable {D : Set (EuclideanSpace ℝ (Fin m))} (hD : MeasurableSet D)
  (t : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) → ℂ)
  (ht : ContDiff ℝ ∞ (Function.uncurry t))
  (hts : HasCompactSupport (Function.uncurry t))
  (T : Lp ℂ 2 (volume.restrict D) →L[ℂ] Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
  (hT : ∀ h, T h =ᵐ[volume] fun x ↦ ∫ u, t x u * h u ∂volume.restrict D)
  (c : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hc : StronglyMeasurable (Function.uncurry c)) (hd : 0 < d)
  {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
  (hs : ∀ u, SupportedInCenteredBox R (c u)) (hf : ∀ u, ContDiff ℝ ∞ (c u))
  (A : ℝ) (hA : 0 ≤ A) (hzero : ∀ u z, ‖c u z‖ ≤ A)
  (hderiv : ∀ u i z,
    ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) (c u) z‖ ≤ A)
  (g : Lp ℂ ∞ (volume.restrict D)) (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)

include hD ht hts hT hc hd hℓ hR hs hf hA hzero hderiv

/-- The normal operator series agrees almost everywhere with the full literal
kernel in `app:ch_osc:eq:two-position-normal-bound`. The actual adjoint and
all integrability premises are derived from the original kernel hypotheses. -/
theorem boxNormalAmplitudeOperator_ae_kernel :
    boxNormalAmplitudeOperator c hc hd hℓ hR hs hf A hA hzero hderiv T g f =ᵐ[volume]
      fullNormalAmplitudeKernel (μ := volume.restrict D) t c g f := by
  have hterms := ae_all_iff.mpr
    (boxNormalAmplitudeTerm_ae_integral hD t ht hts T hT c hc hd hℓ hR hs hf
      A hA hzero hderiv g f)
  filter_upwards [boxNormalAmplitudeOperator_hasSum_ae c hc hd hℓ hR hs hf
    A hA hzero hderiv T g f, hterms] with x hx hterms
  simp_rw [hterms] at hx
  exact hx.unique
    (hasSum_fullNormalAmplitudeKernel_of_integrable_weight t c hc hd hℓ hR hs hf
      hzero hderiv g f x (integrable_fullNormalAmplitudeKernel_weight t ht hts g f x))

/-- The full literal normal kernel belongs to L² on every L² input
(`app:ch_osc:eq:two-position-normal-bound`). -/
theorem memLp_fullNormalAmplitudeKernel :
    MemLp (fullNormalAmplitudeKernel (μ := volume.restrict D) t c g f) 2 :=
  (Lp.memLp _).ae_eq
    (boxNormalAmplitudeOperator_ae_kernel hD t ht hts T hT c hc hd hℓ hR hs hf
      A hA hzero hderiv g f)

/-- The L² class of the literal normal integral in
`app:ch_osc:eq:two-position-normal-bound`. -/
def fullNormalAmplitudeKernelLp : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 :=
  (memLp_fullNormalAmplitudeKernel hD t ht hts T hT c hc hd hℓ hR hs hf
    A hA hzero hderiv g f).toLp _

/-- The L² realization of the full integral equals the normal operator series
(`app:ch_osc:eq:two-position-normal-bound`). -/
theorem fullNormalAmplitudeKernelLp_eq :
    fullNormalAmplitudeKernelLp hD t ht hts T hT c hc hd hℓ hR hs hf A hA hzero hderiv g f =
      boxNormalAmplitudeOperator c hc hd hℓ hR hs hf A hA hzero hderiv T g f := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans
    (boxNormalAmplitudeOperator_ae_kernel hD t ht hts T hT c hc hd hℓ hR hs hf
      A hA hzero hderiv g f).symm

/-- The full literal normal kernel satisfies the L² bound of
`app:ch_osc:eq:two-position-normal-bound`, with the original input operator's
squared norm and the L∞ norm of the mask. -/
theorem norm_fullNormalAmplitudeKernelLp_le :
    ‖fullNormalAmplitudeKernelLp hD t ht hts T hT c hc hd hℓ hR hs hf
      A hA hzero hderiv g f‖ ≤
      (boxAmplitudeConstant d ℓ * A * ‖T‖ ^ 2 * ‖g‖) * ‖f‖ := by
  rw [fullNormalAmplitudeKernelLp_eq]
  exact (ContinuousLinearMap.le_opNorm _ f).trans
    (mul_le_mul_of_nonneg_right
      (norm_boxNormalAmplitudeOperator_le c hc hd hℓ hR hs hf A hA hzero hderiv T g)
      (norm_nonneg f))

end JanetCartan.AmplitudeBound
