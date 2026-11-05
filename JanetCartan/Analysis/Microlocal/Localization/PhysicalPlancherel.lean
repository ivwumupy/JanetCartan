module

public import JanetCartan.Analysis.Microlocal.Localization.Source
public import JanetCartan.Analysis.Microlocal.Localization.RadialIntegral
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Plancherel in physical frequency coordinates

The Fourier normalization used in `app:ch_osc:prop:osc-source-shell` is
`(2π)^(-n) ∫ x, exp(-i x·ξ) h(x)`. Mathlib uses `exp(-2π i x·ξ)`.
We identify the ordinary integral with the L² transform via tempered
distributions, then change frequency variables. Both squared integrability
and the norm identities follow from the L¹ and L² assumptions on the source.

The target may be any complete complex Hilbert space, in particular any
finite-dimensional complex Hilbert space. Its real scalar action is the
canonical restriction of the complex scalar action.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped RealInnerProductSpace ContDiff

namespace JanetCartan.Localization

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The Hilbert-valued ordinary Fourier integral represents the L² transform almost
everywhere (`app:ch_osc:prop:osc-source-shell`). The identification follows from equality
against compactly supported smooth tests, using the tempered-distribution transform. -/
theorem fourierTransform_coeFn_ae_integral_hilbert (f : Lp (α := E) F 2 volume)
    (hf : Integrable (f : E → F)) :
    (𝓕 f : Lp (α := E) F 2 volume) =ᵐ[volume] 𝓕 (f : E → F) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 f)).locallyIntegrable (by norm_num))
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf).locallyIntegrable
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let s := hc'.toSchwartzMap hg'
  have hd := congrArg (fun T : TemperedDistribution E F ↦ T s)
    (Lp.fourier_toTemperedDistribution_eq f)
  have hs := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.lsmul ℂ ℂ) (μ := volume) (ν := volume) (L := innerₗ E)
    Real.continuous_fourierChar continuous_inner s.integrable hf
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hd
  have hs' : (∫ x, (𝓕 s) x • f x) = ∫ x, s x • 𝓕 (f : E → F) x := by
    simpa using! hs
  simpa [s, Function.comp_def] using! hd.symm.trans hs'

omit [CompleteSpace F] in
private theorem integral_norm_sq_Lp (f : Lp (α := E) F 2 volume) : (∫ x, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) f f).symm

/-- `app:ch_osc:prop:osc-source-shell`: The ordinary Fourier integral of an L¹ ∩ L²
function belongs to L², without assuming an identification with the L² transform. -/
theorem fourierIntegral_memLp_two {h : E → F} (hh : Integrable h)
    (h₂ : MemLp h 2 volume) : MemLp (𝓕 h) 2 volume := by
  have hf : Integrable (h₂.toLp h : E → F) := hh.congr h₂.coeFn_toLp.symm
  have he := fourierTransform_coeFn_ae_integral_hilbert (h₂.toLp h) hf
  have he' : (𝓕 (h₂.toLp h) : Lp (α := E) F 2 volume) =ᵐ[volume] 𝓕 h :=
    he.trans (Filter.Eventually.of_forall (Real.fourier_congr_ae h₂.coeFn_toLp))
  exact (memLp_congr_ae he').mp (Lp.memLp (𝓕 (h₂.toLp h)))

omit [CompleteSpace F] in
/-- `app:ch_osc:prop:osc-source-shell`: Conversion from physical frequency to Mathlib's
unit-period frequency. No integrability assumption is needed for this equality of integrals. -/
theorem physicalFourierIntegral_eq_fourier (h : E → F) (ξ : E) :
    physicalFourierIntegral volume h (InnerProductSpace.toDual ℝ E ξ) =
      𝓕 h ((2 * Real.pi)⁻¹ • ξ) := by
  rw [physicalFourierIntegral, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  congr 2
  simp only [phaseOscillation, InnerProductSpace.toDual_apply_apply, real_inner_smul_right]
  congr 2
  rw [real_inner_comm ξ x]
  field_simp

/-- `app:ch_osc:prop:osc-source-shell`: Plancherel for the ordinary Hilbert-valued
Fourier integral in Mathlib's unit-period normalization. -/
theorem integral_norm_sq_fourierIntegral {h : E → F} (hh : Integrable h)
    (h₂ : MemLp h 2 volume) : (∫ ξ, ‖𝓕 h ξ‖ ^ 2) = ∫ x, ‖h x‖ ^ 2 := by
  have hf : Integrable (h₂.toLp h : E → F) := hh.congr h₂.coeFn_toLp.symm
  have he : (𝓕 (h₂.toLp h) : Lp (α := E) F 2 volume) =ᵐ[volume] 𝓕 h :=
    (fourierTransform_coeFn_ae_integral_hilbert (h₂.toLp h) hf).trans
      (Filter.Eventually.of_forall (Real.fourier_congr_ae h₂.coeFn_toLp))
  calc
    _ = ∫ ξ, ‖(𝓕 (h₂.toLp h) : Lp (α := E) F 2 volume) ξ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]
    _ = ‖𝓕 (h₂.toLp h)‖ ^ 2 := integral_norm_sq_Lp _
    _ = ‖h₂.toLp h‖ ^ 2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ x, ‖(h₂.toLp h) x‖ ^ 2 := (integral_norm_sq_Lp _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx]

/-- `app:ch_osc:prop:osc-source-shell`: Squared integrability of the unnormalized
physical Fourier integral of an L¹ ∩ L² source. -/
theorem integrable_norm_sq_physicalFourierIntegral {h : E → F} (hh : Integrable h)
    (h₂ : Integrable (fun x ↦ ‖h x‖ ^ 2)) :
    Integrable (fun ξ ↦ ‖physicalFourierIntegral volume h
      (InnerProductSpace.toDual ℝ E ξ)‖ ^ 2) := by
  have hm := fourierIntegral_memLp_two hh
    ((memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).mpr h₂)
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  simpa only [physicalFourierIntegral_eq_fourier] using
    hi.comp_smul (inv_ne_zero (by positivity : (2 * Real.pi : ℝ) ≠ 0))

/-- `app:ch_osc:prop:osc-source-shell`: Physical-frequency Plancherel, including the
exact Jacobian factor `(2π)^n`. -/
theorem integral_norm_sq_physicalFourierIntegral {h : E → F} (hh : Integrable h)
    (h₂ : Integrable (fun x ↦ ‖h x‖ ^ 2)) :
    (∫ ξ, ‖physicalFourierIntegral volume h (InnerProductSpace.toDual ℝ E ξ)‖ ^ 2) =
      (2 * Real.pi) ^ Module.finrank ℝ E * ∫ x, ‖h x‖ ^ 2 := by
  simp_rw [physicalFourierIntegral_eq_fourier]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun ξ ↦ ‖𝓕 h ξ‖ ^ 2)
      (by positivity : 0 ≤ 2 * Real.pi),
    smul_eq_mul, integral_norm_sq_fourierIntegral hh
      ((memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).mpr h₂)]

/-- `app:ch_osc:prop:osc-source-shell`: The unnormalized physical Fourier L² norm
is `(2π)^(n/2)` times the source L² norm. -/
theorem sqrt_integral_norm_sq_physicalFourierIntegral {h : E → F} (hh : Integrable h)
    (h₂ : Integrable (fun x ↦ ‖h x‖ ^ 2)) :
    Real.sqrt (∫ ξ, ‖physicalFourierIntegral volume h (InnerProductSpace.toDual ℝ E ξ)‖ ^ 2) =
      (2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2) * Real.sqrt (∫ x, ‖h x‖ ^ 2) := by
  rw [integral_norm_sq_physicalFourierIntegral hh h₂, Real.sqrt_mul (by positivity)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- `app:ch_osc:prop:osc-source-shell`: Plancherel in the shared Fourier-weighted
norm API at Sobolev order zero. -/
theorem fourierWeightedL2Norm_zero_physicalFourierIntegral {h : E → F} (hh : Integrable h)
    (h₂ : Integrable (fun x ↦ ‖h x‖ ^ 2)) :
    fourierWeightedL2Norm volume 0
      (fun ξ ↦ physicalFourierIntegral volume h (InnerProductSpace.toDual ℝ E ξ)) =
      (2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2) * Real.sqrt (∫ x, ‖h x‖ ^ 2) := by
  simpa only [fourierWeightedL2Norm, Real.rpow_zero, one_mul] using
    sqrt_integral_norm_sq_physicalFourierIntegral hh h₂

omit [CompleteSpace F] in
/-- `app:ch_osc:prop:osc-source-shell`: The paper additionally multiplies the
physical Fourier integral by `(2π)^(-n)`, written as the inverse of the natural power. -/
theorem paperNormalizedFourierIntegral_eq_fourier (h : E → F) (ξ : E) :
    ((2 * Real.pi) ^ Module.finrank ℝ E)⁻¹ •
      physicalFourierIntegral volume h (InnerProductSpace.toDual ℝ E ξ) =
    ((2 * Real.pi) ^ Module.finrank ℝ E)⁻¹ • 𝓕 h ((2 * Real.pi)⁻¹ • ξ) := by
  rw [physicalFourierIntegral_eq_fourier]

/-- `app:ch_osc:prop:osc-source-shell`: Squared integrability in the paper's
`(2π)^(-n)` normalization. -/
theorem integrable_norm_sq_paperNormalizedFourierIntegral {h : E → F} (hh : Integrable h)
    (h₂ : Integrable (fun x ↦ ‖h x‖ ^ 2)) :
    Integrable (fun ξ ↦ ‖((2 * Real.pi) ^ Module.finrank ℝ E)⁻¹ •
      physicalFourierIntegral volume h (InnerProductSpace.toDual ℝ E ξ)‖ ^ 2) := by
  simp_rw [norm_smul, mul_pow]
  exact (integrable_norm_sq_physicalFourierIntegral hh h₂).const_mul _

/-- `app:ch_osc:prop:osc-source-shell`: The paper's normalized transform has squared
L² norm `(2π)^(-n)` times the squared source norm. -/
theorem integral_norm_sq_paperNormalizedFourierIntegral {h : E → F} (hh : Integrable h)
    (h₂ : Integrable (fun x ↦ ‖h x‖ ^ 2)) :
    (∫ ξ, ‖((2 * Real.pi) ^ Module.finrank ℝ E)⁻¹ •
      physicalFourierIntegral volume h (InnerProductSpace.toDual ℝ E ξ)‖ ^ 2) =
      ((2 * Real.pi) ^ Module.finrank ℝ E)⁻¹ * ∫ x, ‖h x‖ ^ 2 := by
  simp_rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ ((2 * Real.pi) ^ Module.finrank ℝ E)⁻¹), mul_pow]
  rw [integral_const_mul, integral_norm_sq_physicalFourierIntegral hh h₂]
  field_simp
  simp only [mul_pow]

/-- `app:ch_osc:prop:osc-source-shell`: The paper's normalized transform has L² norm
`(2π)^(-n/2)` times the source norm. -/
theorem sqrt_integral_norm_sq_paperNormalizedFourierIntegral {h : E → F} (hh : Integrable h)
    (h₂ : Integrable (fun x ↦ ‖h x‖ ^ 2)) :
    Real.sqrt (∫ ξ, ‖((2 * Real.pi) ^ Module.finrank ℝ E)⁻¹ •
      physicalFourierIntegral volume h (InnerProductSpace.toDual ℝ E ξ)‖ ^ 2) =
      (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.sqrt (∫ x, ‖h x‖ ^ 2) := by
  rw [integral_norm_sq_paperNormalizedFourierIntegral hh h₂, Real.sqrt_mul (by positivity)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg (by positivity),
    ← Real.rpow_mul (by positivity)]
  congr 1
  ring

end JanetCartan.Localization

