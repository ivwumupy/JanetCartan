module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.FirstDerivatives.Coordinates

/-!
# Source integration by parts for weak L² derivatives

The compact source kernels in `app:ch_response:eq:direct-envelope-profile`
can be tested against arbitrary scalar Euclidean L² data and their actual
distributional derivatives. Regard the smooth compact kernel as a Schwartz
test and evaluate the defining equality of tempered distributions. This gives
physical coordinate differentiation with respect to Lebesgue measure, with
no Fourier normalization factor.

The consumer is the construction of `HasParameterAmplitudeTransfer`: apply
these lemmas to a fixed frequency slice of the full scalar kernel, including
its `C` or `C B⁻¹` coefficient product. Smoothness and compact support of that
slice are supplied by the kernel construction; no operator realization or
phase identity is needed here.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff SchwartzMap LineDeriv

namespace JanetCartan.ResponseTransfer.NearCarrierParameter

open Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The compact test kernel times any scalar L² representative is integrable.
This justifies the source pairing in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem integrable_compactTest_mul_l2
    (f : Lp ℂ 2 (volume : Measure E))
    (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) :
    Integrable (fun x ↦ b x * f x) (volume : Measure E) := by
  exact ((hbc.toSchwartzMap hb).memLp 2).integrable_mul (Lp.memLp f)

/-- The physical coordinate derivative of the compact test kernel times any
scalar L² representative is integrable. This justifies the differentiated
source pairing in `app:ch_response:eq:direct-envelope-profile`. -/
theorem integrable_compactTest_fderiv_mul_l2
    (f : Lp ℂ 2 (volume : Measure E)) (i : Fin d)
    (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) :
    Integrable (fun x ↦ fderiv ℝ b x (EuclideanSpace.single i 1) * f x)
      (volume : Measure E) := by
  let φ : 𝓢(E, ℂ) := hbc.toSchwartzMap hb
  have hi := ((∂_{(EuclideanSpace.single i 1 : E)} φ).memLp 2).integrable_mul (Lp.memLp f)
  simpa only [Pi.mul_def, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    show (φ : E → ℂ) = b from rfl] using hi

/-- Evaluate the actual tempered-distribution derivative on a smooth compact
complex test kernel. This is source integration by parts for arbitrary L²
data in `app:ch_response:eq:direct-envelope-profile`, with the physical
coordinate derivative and literal Euclidean Lebesgue measure. -/
theorem integral_compactTest_mul_weakDerivative
    {f g : Lp ℂ 2 (volume : Measure E)} {i : Fin d}
    (h : HasEuclideanL2CoordinateDerivative i f g)
    (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) :
    (∫ x, b x * g x) =
      -(∫ x, fderiv ℝ b x (EuclideanSpace.single i 1) * f x) := by
  let φ : 𝓢(E, ℂ) := hbc.toSchwartzMap hb
  have he := congrArg (fun T : 𝓢'(E, ℂ) ↦ T φ) h
  change (∂_{EuclideanSpace.basisFun (Fin d) ℝ i} (f : 𝓢'(E, ℂ))) φ = _ at he
  rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
    Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at he
  simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    EuclideanSpace.basisFun_apply, smul_eq_mul,
    show (φ : E → ℂ) = b from rfl] using he.symm

/-- Transfer a physical source derivative off the compact test kernel and
onto the datum's actual weak L² derivative, with the negative sign required
in `app:ch_response:eq:direct-envelope-profile`. -/
theorem integral_compactTest_fderiv_mul_l2
    {f g : Lp ℂ 2 (volume : Measure E)} {i : Fin d}
    (h : HasEuclideanL2CoordinateDerivative i f g)
    (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) :
    (∫ x, fderiv ℝ b x (EuclideanSpace.single i 1) * f x) =
      -(∫ x, b x * g x) := by
  exact neg_eq_iff_eq_neg.mp (integral_compactTest_mul_weakDerivative h b hb hbc).symm

end JanetCartan.ResponseTransfer.NearCarrierParameter
