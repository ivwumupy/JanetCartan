module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Differentiation.Linearity
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Differentiation.Regularity

/-!
# Operator norm differentiation of compact scalar kernels

The fixed frequency parameter differentiation assertion in Step 2 of
`app:ch_osc:prop:osc-normal`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace JanetCartan.NormalComparison

variable {d m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "U" => EuclideanSpace ℝ (Fin m)
variable {μ : Measure (EuclideanSpace ℝ (Fin m))}
  {ν : Measure (EuclideanSpace ℝ (Fin d))}
  [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [SFinite μ] [SFinite ν]

/-- Operator norm differentiation from a jointly continuous pointwise parameter
derivative on fixed compact spatial supports (`app:ch_osc:prop:osc-normal`). -/
theorem hasDerivAt_compactKernelOperator_of_continuous_derivative
    {t t' : ℝ → E × U → ℂ}
    (ht : ∀ s, Continuous (t s)) (hts : ∀ s, HasCompactSupport (t s))
    (ht' : ∀ s, Continuous (t' s)) (hts' : ∀ s, HasCompactSupport (t' s))
    {K : Set (E × U)} (hK : IsCompact K)
    (hs : ∀ s z, z ∉ K → t s z = 0)
    (hd : ∀ s z, HasDerivAt (fun r ↦ t r z) (t' s z) s)
    (hc : Continuous (Function.uncurry t')) (s₀ : ℝ) :
    HasDerivAt
      (fun s ↦ compactKernelOperator (μ := μ) (ν := ν)
        (t := fun x u ↦ t s (x, u)) (ht s) (hts s))
      (compactKernelOperator (μ := μ) (ν := ν)
        (t := fun x u ↦ t' s₀ (x, u)) (ht' s₀) (hts' s₀)) s₀ := by
  let A := Prod.fst '' K
  let B := Prod.snd '' K
  have hA : IsCompact A := hK.image continuous_fst
  have hB : IsCompact B := hK.image continuous_snd
  let a := ‖indicatorConstLp (μ := ν) 2 hA.measurableSet hA.measure_lt_top.ne (1 : ℝ)‖
  let b := ‖indicatorConstLp (μ := μ) 2 hB.measurableSet hB.measure_lt_top.ne (1 : ℝ)‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hcpos
  let ε := c / (a * b + 1)
  have hε : 0 < ε := div_pos hcpos (by positivity)
  filter_upwards [eventually_uniform_parameter_remainder hK hs hd hc s₀ hε] with s hsrem
  let R : E → U → ℂ := fun x u ↦ t s (x, u) - t s₀ (x, u) - (s - s₀) • t' s₀ (x, u)
  have hRc : Continuous (Function.uncurry R) := by
    convert (ht s |>.sub (ht s₀)).sub
      ((continuous_const (y := s - s₀)).smul (ht' s₀)) using 1
    rfl
  have hRs : HasCompactSupport (Function.uncurry R) :=
    (hts s |>.sub (hts s₀)).sub ((hts' s₀).smul_left (f := fun _ ↦ s - s₀))
  have hRzero (z : E × U) (hz : z ∉ K) : R z.1 z.2 = 0 := by
    simp [R, hs s z hz, hs s₀ z hz, parameterDerivative_eq_zero_off_support hs hd s₀ hz]
  have hRsupp : Function.support (Function.uncurry R) ⊆ A ×ˢ B := by
    intro z hz
    have hzK : z ∈ K := by
      by_contra hn
      exact hz (hRzero z hn)
    exact ⟨⟨z, hzK, rfl⟩, ⟨z, hzK, rfl⟩⟩
  have hop := norm_compactKernelOperator_le_fixedSupport (μ := μ) (ν := ν)
    hRc hRs hA hB hRsupp (mul_nonneg hε.le (norm_nonneg (s - s₀)))
    (fun x u ↦ hsrem (x, u))
  have heq : compactKernelOperator (μ := μ) (ν := ν) hRc hRs =
      compactKernelOperator (μ := μ) (ν := ν) (t := fun x u ↦ t s (x, u)) (ht s) (hts s) -
      compactKernelOperator (μ := μ) (ν := ν) (t := fun x u ↦ t s₀ (x, u)) (ht s₀) (hts s₀) -
      (s - s₀) • compactKernelOperator (μ := μ) (ν := ν)
        (t := fun x u ↦ t' s₀ (x, u)) (ht' s₀) (hts' s₀) := by
    exact compactKernelOperator_remainder
      (t := fun x u ↦ t s (x, u)) (v := fun x u ↦ t s₀ (x, u))
      (w := fun x u ↦ t' s₀ (x, u)) (R := R) (ht s) (ht s₀) (ht' s₀) hRc
      (hts s) (hts s₀) (hts' s₀) hRs (s - s₀) (fun _ _ ↦ rfl)
  rw [heq] at hop
  refine hop.trans ?_
  change ε * ‖s - s₀‖ * a * b ≤ c * ‖s - s₀‖
  have hεab : ε * (a * b) ≤ c := by
    have hle : a * b ≤ a * b + 1 := by linarith
    calc
      ε * (a * b) ≤ ε * (a * b + 1) := mul_le_mul_of_nonneg_left hle hε.le
      _ = c := div_mul_cancel₀ c (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hεab (norm_nonneg (s - s₀))]

/-- The actual compact integral operators of a jointly C¹ kernel family are
parameter differentiable in operator norm. The derivative is the constructed
operator for the actual parameter derivative. All continuity and support facts
are derived from the stated smoothness and fixed support assumptions
(`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem hasDerivAt_compactKernelOperator {t : ℝ → E × U → ℂ}
    (ht : ContDiff ℝ 1 (Function.uncurry t)) {K : Set (E × U)} (hK : IsCompact K)
    (hs : ∀ s z, z ∉ K → t s z = 0) (s₀ : ℝ) :
    HasDerivAt
      (fun s ↦ compactKernelOperator (μ := μ) (ν := ν) (t := fun x u ↦ t s (x, u))
        (continuous_kernelSlice ht s) (hasCompactSupport_kernelSlice hK hs s))
      (compactKernelOperator (μ := μ) (ν := ν)
        (t := fun x u ↦ kernelParameterDeriv t s₀ (x, u))
        (continuous_kernelParameterDeriv_slice ht s₀)
        (hasCompactSupport_kernelParameterDeriv ht hK hs s₀)) s₀ :=
  hasDerivAt_compactKernelOperator_of_continuous_derivative
    (continuous_kernelSlice ht) (hasCompactSupport_kernelSlice hK hs)
    (continuous_kernelParameterDeriv_slice ht) (hasCompactSupport_kernelParameterDeriv ht hK hs)
    hK hs (hasDerivAt_kernelParameterDeriv ht) (continuous_kernelParameterDeriv ht) s₀

end JanetCartan.NormalComparison
