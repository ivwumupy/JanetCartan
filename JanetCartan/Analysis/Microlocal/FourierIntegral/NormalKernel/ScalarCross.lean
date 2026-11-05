module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.FullKernel

/-!
# Unweighted compact cross kernels

Specializations of the existing compact-kernel Fubini theorem to full Euclidean
Lebesgue measure, used in `app:ch_regular_base:eq:actual-normal-kernel`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace JanetCartan.FourierIntegral.NormalKernel

open NormalComparison

variable {n : ℕ} {s t : Euclidean n → Euclidean n → ℂ}

/-- Absolute convergence of the scalar cross-normal action before Fubini;
no spatial source cutoff is present (`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem integrable_cross_weight
    (hcS : Continuous (Function.uncurry s)) (hsS : HasCompactSupport (Function.uncurry s))
    (hcT : Continuous (Function.uncurry t)) (hsT : HasCompactSupport (Function.uncurry t))
    (f : Lp (α := Euclidean n) ℂ 2) (x : Euclidean n) :
    Integrable (fun p : Euclidean n × Euclidean n ↦
      s x p.2 * star (t p.1 p.2) * f p.1) (volume.prod volume) := by
  let g : Lp (α := Euclidean n) ℂ ∞ (volume.restrict Set.univ) :=
    (memLp_top_const (1 : ℂ)).toLp _
  have hg : g =ᵐ[volume] fun _ ↦ (1 : ℂ) := by
    simpa only [Measure.restrict_univ] using
      (memLp_top_const (μ := volume.restrict Set.univ) (1 : ℂ)).coeFn_toLp
  have h := integrable_compactCrossKernel_weight Set.univ hcS hsS hcT hsT g f x
  simp only [Measure.restrict_univ] at h
  apply h.congr
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae_eq_comp hg] with p hp
  dsimp only [Function.comp_def] at hp
  simp only [hp, mul_one]

/-- Absolute convergence of each frequency section of the pure cross normal
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem integrable_cross_section
    (hcS : Continuous (Function.uncurry s)) (hsS : HasCompactSupport (Function.uncurry s))
    (hcT : Continuous (Function.uncurry t)) (hsT : HasCompactSupport (Function.uncurry t))
    (x y : Euclidean n) : Integrable (fun ξ ↦ s x ξ * star (t y ξ)) := by
  let g : Lp (α := Euclidean n) ℂ ∞ (volume.restrict Set.univ) :=
    (memLp_top_const (1 : ℂ)).toLp _
  have hg : g =ᵐ[volume] fun _ ↦ (1 : ℂ) := by
    simpa only [Measure.restrict_univ] using
      (memLp_top_const (μ := volume.restrict Set.univ) (1 : ℂ)).coeFn_toLp
  have h := integrable_compactCrossKernel_section Set.univ hcS hsS hcT hsT g x y
  simp only [Measure.restrict_univ] at h
  apply h.congr
  filter_upwards [hg] with ξ hξ
  simp only [hξ, mul_one]

/-- The cross kernel acts absolutely on each L² input, allowing the finite
matrix sums to pass through the output integral
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem integrable_cross_action
    (hcS : Continuous (Function.uncurry s)) (hsS : HasCompactSupport (Function.uncurry s))
    (hcT : Continuous (Function.uncurry t)) (hsT : HasCompactSupport (Function.uncurry t))
    (f : Lp (α := Euclidean n) ℂ 2) (x : Euclidean n) :
    Integrable (fun y ↦ (∫ ξ, s x ξ * star (t y ξ)) * f y) := by
  simpa only [integral_mul_const] using
    (integrable_cross_weight hcS hsS hcT hsT f x).integral_prod_left

/-- The scalar pure cross-normal kernel is obtained by actual adjoints and
absolutely convergent Fubini, using the existing compact-kernel adjoint theorem
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem compactKernel_cross_ae
    (hcS : Continuous (Function.uncurry s)) (hsS : HasCompactSupport (Function.uncurry s))
    (hcT : Continuous (Function.uncurry t)) (hsT : HasCompactSupport (Function.uncurry t))
    (f : Lp (α := Euclidean n) ℂ 2) :
    compactKernelOperator (μ := volume) (ν := volume) hcS hsS ((compactKernelOperator (μ := volume) (ν := volume) hcT hsT).adjoint f) =ᵐ[volume]
      fun x ↦ ∫ y, (∫ ξ, s x ξ * star (t y ξ)) * f y := by
  have hadj := compactKernelOperator_adjoint_ae_integral (μ := volume) hcT hsT f
  filter_upwards [compactKernelOperator_ae_integral (ν := volume) hcS hsS
    ((compactKernelOperator (μ := volume) (ν := volume) hcT hsT).adjoint f)] with x hx
  rw [hx]
  calc
    _ = ∫ ξ, s x ξ * ∫ y, star (t y ξ) * f y := by
      apply integral_congr_ae
      filter_upwards [hadj] with ξ hξ
      rw [hξ]
    _ = ∫ ξ, ∫ y, s x ξ * star (t y ξ) * f y := by
      simp only [← integral_const_mul, mul_assoc]
    _ = ∫ y, ∫ ξ, s x ξ * star (t y ξ) * f y :=
      (integral_integral_swap (integrable_cross_weight hcS hsS hcT hsT f x)).symm
    _ = _ := by simp only [integral_mul_const]

end JanetCartan.FourierIntegral.NormalKernel
