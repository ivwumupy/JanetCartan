module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Differentiation.UniformRemainder
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Parameter derivatives of smooth compact kernels

Continuity and compact support of the actual parameter derivative, for
`app:ch_osc:prop:osc-normal`.
-/

@[expose] public noncomputable section

open scoped Topology ContDiff

namespace JanetCartan.NormalComparison

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The actual parameter derivative, obtained by evaluating the total derivative
in the parameter direction (`app:ch_osc:prop:osc-normal`). -/
def kernelParameterDeriv (t : ℝ → Z → ℂ) (s : ℝ) (z : Z) : ℂ :=
  fderiv ℝ (Function.uncurry t) (s, z) (1, 0)

/-- Chain rule identifying the parameter derivative in
`app:ch_osc:prop:osc-normal`. -/
theorem hasDerivAt_kernelParameterDeriv {t : ℝ → Z → ℂ}
    (ht : ContDiff ℝ 1 (Function.uncurry t)) (s : ℝ) (z : Z) :
    HasDerivAt (fun r ↦ t r z) (kernelParameterDeriv t s z) s := by
  exact ((ht.differentiable (by norm_num)) (s, z)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))

/-- The total-derivative formula is the ordinary scalar parameter derivative
(`app:ch_osc:prop:osc-normal`). -/
theorem kernelParameterDeriv_eq_deriv {t : ℝ → Z → ℂ}
    (ht : ContDiff ℝ 1 (Function.uncurry t)) (s : ℝ) (z : Z) :
    kernelParameterDeriv t s z = deriv (fun r ↦ t r z) s :=
  (hasDerivAt_kernelParameterDeriv ht s z).deriv.symm

/-- Joint continuity of the parameter derivative follows from joint C¹
regularity, as needed in `app:ch_osc:prop:osc-normal`. -/
theorem continuous_kernelParameterDeriv {t : ℝ → Z → ℂ}
    (ht : ContDiff ℝ 1 (Function.uncurry t)) :
    Continuous (Function.uncurry (kernelParameterDeriv t)) :=
  (ht.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- The parameter derivative inherits the fixed spatial support in
`app:ch_osc:prop:osc-normal`. -/
theorem kernelParameterDeriv_eq_zero {t : ℝ → Z → ℂ} {K : Set Z}
    (ht : ContDiff ℝ 1 (Function.uncurry t))
    (hs : ∀ s z, z ∉ K → t s z = 0) (s : ℝ) {z : Z} (hz : z ∉ K) :
    kernelParameterDeriv t s z = 0 :=
  parameterDerivative_eq_zero_off_support hs (hasDerivAt_kernelParameterDeriv ht) s hz

/-- Compact support of each derivative kernel is derived from the common
support of the original family (`app:ch_osc:prop:osc-normal`). -/
theorem hasCompactSupport_kernelParameterDeriv {t : ℝ → Z → ℂ} {K : Set Z}
    (ht : ContDiff ℝ 1 (Function.uncurry t)) (hK : IsCompact K)
    (hs : ∀ s z, z ∉ K → t s z = 0) (s : ℝ) :
    HasCompactSupport (kernelParameterDeriv t s) := by
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz
  by_contra hn
  exact hz (kernelParameterDeriv_eq_zero ht hs s hn)

/-- Continuity of a spatial slice of a C¹ kernel family
(`app:ch_osc:prop:osc-normal`). -/
theorem continuous_kernelSlice {t : ℝ → Z → ℂ}
    (ht : ContDiff ℝ 1 (Function.uncurry t)) (s : ℝ) : Continuous (t s) :=
  ht.continuous.comp (continuous_const.prodMk continuous_id)

omit [NormedSpace ℝ Z] in
/-- Each spatial slice has compact support from the fixed support assumption
of `app:ch_osc:prop:osc-normal`. -/
theorem hasCompactSupport_kernelSlice {t : ℝ → Z → ℂ} {K : Set Z}
    (hK : IsCompact K) (hs : ∀ s z, z ∉ K → t s z = 0) (s : ℝ) :
    HasCompactSupport (t s) := by
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz
  by_contra hn
  exact hz (hs s z hn)

/-- Continuity of a spatial slice of the actual parameter derivative
(`app:ch_osc:prop:osc-normal`). -/
theorem continuous_kernelParameterDeriv_slice {t : ℝ → Z → ℂ}
    (ht : ContDiff ℝ 1 (Function.uncurry t)) (s : ℝ) :
    Continuous (kernelParameterDeriv t s) :=
  (continuous_kernelParameterDeriv ht).comp (continuous_const.prodMk continuous_id)

end JanetCartan.NormalComparison
