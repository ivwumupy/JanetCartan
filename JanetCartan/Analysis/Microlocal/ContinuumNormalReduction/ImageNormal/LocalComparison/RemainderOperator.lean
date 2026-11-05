module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeRemainder
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Realization.CompactKernel

/-!
# Bounded realization and literal adjoint of the local Bessel remainder

The concrete smooth compact kernel gives a bounded operator on the full
Euclidean complex L² space, using Lebesgue measure. Its Hilbert adjoint is
integration against the literal reversed kernel. These are the bounded
error operators in `app:ch_background:prop:bg-frame`, Step 1.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
open ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem continuous_complex_remainder
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r) :
    Continuous (fun p : E × E ↦ (localizedImageBesselRemainder χ ψ p.1 p.2 : ℂ)) :=
  Complex.continuous_ofReal.comp
    (contDiff_localizedImageBesselRemainder hr χ ψ hχ hψ hχs hψs).continuous

private theorem compactSupport_complex_remainder
    {r : ℝ} (χ ψ : E → ℝ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r) :
    HasCompactSupport (fun p : E × E ↦ (localizedImageBesselRemainder χ ψ p.1 p.2 : ℂ)) :=
  (hasCompactSupport_localizedImageBesselRemainder_of_cube_support χ ψ hχs hψs).comp_left
    (by simp : ((0 : ℝ) : ℂ) = 0)

variable {r : ℝ} (hr : r < 1 / 2) (χ ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r)

/-- The actual local Bessel remainder on Euclidean L²
(`app:ch_background:prop:bg-frame`, Step 1). Boundedness is constructed from
the smooth compact kernel; no operator estimate is a premise. -/
def localizedImageBesselRemainderOperator : Lp ℂ 2 (volume : Measure E) →L[ℂ]
    Lp ℂ 2 (volume : Measure E) :=
  compactKernelOperator (t := fun x y : E ↦ (localizedImageBesselRemainder χ ψ x y : ℂ))
    (μ := volume) (ν := volume)
    (Complex.continuous_ofReal.comp
      (contDiff_localizedImageBesselRemainder hr χ ψ hχ hψ hχs hψs).continuous)
    ((hasCompactSupport_localizedImageBesselRemainder_of_cube_support χ ψ hχs hψs).comp_left
      (by simp : ((0 : ℝ) : ℂ) = 0))

/-- The bounded error operator has the stated kernel on every L² input,
with absolute convergence (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem localizedImageBesselRemainderOperator_ae_integral (f : Lp ℂ 2 (volume : Measure E)) :
    localizedImageBesselRemainderOperator hr χ ψ hχ hψ hχs hψs f =ᵐ[volume]
      fun x ↦ ∫ y : E, (localizedImageBesselRemainder χ ψ x y : ℂ) * f y :=
  compactKernelOperator_ae_integral _ _ f

include hr hχ hψ hχs hψs in
/-- Absolute convergence of the local error integral for every L² input
and every evaluation point (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integrable_localizedImageBesselRemainder_mul_L2
    (f : Lp ℂ 2 (volume : Measure E)) (x : E) :
    Integrable (fun y : E ↦ (localizedImageBesselRemainder χ ψ x y : ℂ) * f y) :=
  integrable_compactKernel_mul_L2
    (t := fun x y : E ↦ (localizedImageBesselRemainder χ ψ x y : ℂ))
    (continuous_complex_remainder hr χ ψ hχ hψ hχs hψs)
    (compactSupport_complex_remainder χ ψ hχs hψs) f x

/-- The literal Hilbert adjoint integrates the reversed scalar kernel
(`app:ch_background:prop:bg-frame`, Step 1); its order is not replaced by
a symbolic transpose or a presumed self-adjointness. -/
theorem localizedImageBesselRemainderOperator_adjoint_ae_integral
    (f : Lp ℂ 2 (volume : Measure E)) :
    (localizedImageBesselRemainderOperator hr χ ψ hχ hψ hχs hψs).adjoint f =ᵐ[volume]
      fun y ↦ ∫ x : E, (localizedImageBesselRemainder χ ψ x y : ℂ) * f x := by
  simpa only [localizedImageBesselRemainderOperator, Complex.star_def, Complex.conj_ofReal] using
    compactKernelOperator_adjoint_ae_integral
      (t := fun x y : E ↦ (localizedImageBesselRemainder χ ψ x y : ℂ))
      (μ := volume) (ν := volume)
      (continuous_complex_remainder hr χ ψ hχ hψ hχs hψs)
      (compactSupport_complex_remainder χ ψ hχs hψs) f

/-- The adjoint of the localized remainder swaps the two actual masks,
by the proved lattice reflection identity
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem localizedImageBesselRemainderOperator_adjoint :
    (localizedImageBesselRemainderOperator hr χ ψ hχ hψ hχs hψs).adjoint =
      localizedImageBesselRemainderOperator hr ψ χ hψ hχ hψs hχs := by
  ext1 f
  apply Lp.ext
  filter_upwards [localizedImageBesselRemainderOperator_adjoint_ae_integral
    hr χ ψ hχ hψ hχs hψs f,
    localizedImageBesselRemainderOperator_ae_integral hr ψ χ hψ hχ hψs hχs f]
    with y hy hy'
  rw [hy, hy']
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedImageBesselRemainder_swap]

end JanetCartan.ContinuumNormalReduction.ImageNormal
