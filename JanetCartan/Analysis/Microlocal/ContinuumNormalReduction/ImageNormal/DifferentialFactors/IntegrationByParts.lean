module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.DifferentialFactors.Amplitude
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Transport.CompactSupport

/-!
# Integration by parts for the image differential factors

The divergence-form source factor of `app:ch_background:prop:bg-frame`,
Step 1, is transferred onto the Fourier phase. Compact support belongs to
the actual test factor; no formal-adjoint identity is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- One entry of the literal divergence-form adjoint, tested against an
arbitrary smooth function. All integrability and boundary cancellation follow
from the compact test (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_divergenceCoefficient (f v : E → ℂ) (A Z : E → ℝ)
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hA : ContDiff ℝ ∞ A) (hZ : ContDiff ℝ ∞ Z) (a : Fin d) :
    (∫ y, f y * (-partialDeriv (fun z ↦ (A z : ℂ) * v z) y a + Z y * v y)) =
      ∫ y, ((A y : ℂ) * partialDeriv f y a + Z y * f y) * v y := by
  have hAv : ContDiff ℝ ∞ (fun y ↦ (A y : ℂ) * v y) :=
    (Complex.ofRealCLM.contDiff.comp hA).mul hv
  have hZc : ContDiff ℝ ∞ (fun y ↦ (Z y : ℂ)) := Complex.ofRealCLM.contDiff.comp hZ
  have hdAv : Continuous (fun y ↦ partialDeriv (fun z ↦ (A z : ℂ) * v z) y a) :=
    (hAv.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdf : Continuous (fun y ↦ partialDeriv f y a) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi₁ : Integrable (fun y ↦ f y * partialDeriv (fun z ↦ (A z : ℂ) * v z) y a) := (hf.continuous.mul hdAv).integrable_of_hasCompactSupport
    ((hc.mul_left.fderiv_apply ℝ (EuclideanSpace.single a 1)).mul_left)
  have hi₂ : Integrable (fun y ↦ f y * Z y * v y) := ((hf.continuous.mul hZc.continuous).mul hv.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hi₃ : Integrable (fun y ↦ partialDeriv f y a * ((A y : ℂ) * v y)) := (hdf.mul hAv.continuous).integrable_of_hasCompactSupport hc.mul_left.mul_left
  calc
    _ = -(∫ y, f y * partialDeriv (fun z ↦ (A z : ℂ) * v z) y a) +
        ∫ y, f y * Z y * v y := by
      simp only [mul_add, mul_neg, ← mul_assoc]
      simpa only [Pi.neg_apply, integral_neg] using integral_add hi₁.neg hi₂
    _ = (∫ y, partialDeriv f y a * ((A y : ℂ) * v y)) +
        ∫ y, f y * Z y * v y := by
      rw [NormalComparison.CompactTransport.integral_mul_partialDeriv hf hAv hc.mul_left a,
        neg_neg]
    _ = _ := by
      rw [← integral_add hi₃ hi₂]
      congr 1
      funext y
      ring

/-- Differentiation in the source position gives `-i kₐ`, fixing the sign
of the image leading term (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem partialDeriv_sourceFourierPhase (x y ξ : E) (a : Fin d) :
    partialDeriv (fun z ↦ (Real.fourierChar ⟪ξ, x - z⟫ : ℂ)) y a =
      (Real.fourierChar ⟪ξ, x - y⟫ : ℂ) *
        (-Complex.I * (((2 * Real.pi) • ξ) a : ℝ)) := by
  have he (z : E) : ⟪ξ, x - z⟫ = ⟪-ξ, z - x⟫ := by
    simp only [inner_sub_right, inner_neg_left]
    ring
  simp_rw [he]
  have h := partialDeriv_source_phase (fun _ : E ↦ 1) y x (-ξ)
    (differentiableAt_const 1) a
  simpa [partialDeriv, PiLp.smul_apply, mul_comm, mul_left_comm, mul_assoc] using h

/-- The source divergence factor really produces `-i kₐ A + Z` after
integration by parts, with its measurement mask included in the compact test
`v` (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_sourcePhase_divergenceCoefficient (x ξ : E) (v : E → ℂ)
    (A Z : E → ℝ) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hA : ContDiff ℝ ∞ A) (hZ : ContDiff ℝ ∞ Z) (a : Fin d) :
    (∫ y, (Real.fourierChar ⟪ξ, x - y⟫ : ℂ) *
      (-partialDeriv (fun z ↦ (A z : ℂ) * v z) y a + Z y * v y)) =
    ∫ y, (Real.fourierChar ⟪ξ, x - y⟫ : ℂ) *
      (-Complex.I * (((2 * Real.pi) • ξ) a : ℝ) * A y + Z y) * v y := by
  have hf : ContDiff ℝ ∞ (fun y ↦ (Real.fourierChar ⟪ξ, x - y⟫ : ℂ)) := by
    exact Pseudodifferential.contDiff_fourierChar.comp ((innerSL ℝ ξ).contDiff.comp
      (contDiff_const.sub contDiff_id))
  rw [integral_divergenceCoefficient _ v A Z hf hv hc hA hZ a]
  congr 1
  funext y
  rw [partialDeriv_sourceFourierPhase]
  ring

end JanetCartan.ContinuumNormalReduction.ImageNormal
