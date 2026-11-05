module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.HalfSpace.Basic

/-!
# Unscaled phases and a fixed amplitude offset

The frequency and derivative bookkeeping in
`app:ch_regular:lem:finite-chain`, “A common kernel estimate”. The phase
gradient and amplitude profiles are geometric derivative bounds. Reciprocal
coefficient bounds and transposed amplitude bounds are derived by the existing
localization API, rather than assumed as integral estimates.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.FiniteChain.Retarded.HalfSpace

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

/-- The derivative-dependent constant for `app:ch_regular:eq:chain-tail`.
It is independent of `L`, `R`, the fixed amplitude offset, and any external
parameter for which the same derivative profiles and gap hold. -/
def decayConstant (e : ι → E) (δ G : ℝ) (P A : ℕ → ℝ) (q : ℕ) : ℝ :=
  Localization.transposeDerivativeConstant e
    (Localization.phaseCoefficientDerivativeBound e δ G P) A q 0

omit [FiniteDimensional ℝ E] in
/-- `app:ch_regular:lem:finite-chain`: nonnegative amplitude profiles give
a nonnegative explicit decay constant. -/
theorem decayConstant_nonneg (e : ι → E) (δ G : ℝ) (P A : ℕ → ℝ)
    (hA : ∀ r, 0 ≤ A r) (q : ℕ) : 0 ≤ decayConstant e δ G P A q :=
  Localization.transposeDerivativeConstant_nonneg e
    (Localization.phaseCoefficientDerivativeBound_nonneg e δ G P) hA q 0

omit [FiniteDimensional ℝ E] in
/-- `app:ch_regular:lem:finite-chain`: scaling the phase by the frequency
scales the squared directional gradient by its square. -/
theorem phaseGradientSquare_frequency (e : ι → E) (F : E → ℝ)
    {x : E} (hF : DifferentiableAt ℝ F x) (R : ℝ) :
    Localization.phaseGradientSquare e (R • F) x =
      R ^ 2 * Localization.phaseGradientSquare e F x := by
  simp only [Localization.phaseGradientSquare, fderiv_const_smul hF,
    smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- `app:ch_regular:lem:finite-chain`: quantitative whole-space integration
with unscaled phase, explicit common compact support, joint gradient derivative
profile `P`, and amplitude profile `A`. The fixed loss `b` is independent of
the integration order `q`. The same constant applies to every external parameter
satisfying these hypotheses. -/
theorem norm_oscillatoryIntegral_le {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (e : ι → E) (F : E → ℝ) (a : E → ℂ)
    (hF : ContDiffOn ℝ ∞ F U) (ha : ContDiffOn ℝ ∞ a U)
    (hsU : tsupport a ⊆ U) (hsK : tsupport a ⊆ K)
    {δ G L R : ℝ} (hδ : 0 < δ) (hL : 1 ≤ L) (hR : 1 ≤ R)
    (hgap : ∀ x ∈ U, δ ≤ Localization.phaseGradientSquare e F x)
    (hupper : ∀ x ∈ U, ‖fderiv ℝ F x‖ ≤ G)
    {P A : ℕ → ℝ} (hA : ∀ r, 0 ≤ A r) (b q : ℕ)
    (hp : ∀ x ∈ tsupport a, ∀ r,
      ‖iteratedFDeriv ℝ r (fderiv ℝ F) x‖ ≤ P r * L ^ r)
    (ha_bound : ∀ x ∈ tsupport a, ∀ r,
      ‖iteratedFDeriv ℝ r a x‖ ≤ A r * L ^ (r + b)) :
    ‖∫ x, Localization.phaseOscillation (R • F) x * a x ∂μ‖ ≤
      (decayConstant e δ G P A q * μ.real K) * L ^ b * (L / R) ^ q := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hFd (x : E) (hx : x ∈ U) : DifferentiableAt ℝ F x :=
    (hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hscaledGap (x : E) (hx : x ∈ U) :
      δ * R ^ 2 ≤ Localization.phaseGradientSquare e (R • F) x := by
    rw [phaseGradientSquare_frequency e F (hFd x hx)]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right (hgap x hx) (sq_nonneg R)
  have hscaledUpper (x : E) (hx : x ∈ U) : ‖fderiv ℝ (R • F) x‖ ≤ G * R := by
    rw [fderiv_const_smul (hFd x hx), norm_smul, Real.norm_eq_abs,
      abs_of_pos hR0]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hupper x hx) hR0.le
  have hscaledProfile (x : E) (hx : x ∈ tsupport a) (j : ℕ) (_ : 1 ≤ j) :
      ‖iteratedFDeriv ℝ (j + 1) (R • F) x‖ ≤ P j * R * L ^ j := by
    rw [iteratedFDeriv_const_smul_apply
      ((hF.contDiffAt (hU.mem_nhds (hsU hx))).of_le (by simp)),
      norm_smul, Real.norm_eq_abs, abs_of_pos hR0]
    have hpj := hp x hx j
    rw [norm_iteratedFDeriv_fderiv] at hpj
    calc
      _ ≤ R * (P j * L ^ j) := mul_le_mul_of_nonneg_left hpj hR0.le
      _ = _ := by ring
  have hamplitude (x : E) (hx : x ∈ tsupport a) (r : ℕ) :
      ‖iteratedFDeriv ℝ r a x‖ ≤ A r * (L ^ b * L ^ r) := by
    simpa only [pow_add, mul_comm (L ^ r) (L ^ b)] using ha_bound x hx r
  have hc : HasCompactSupport a := hK.of_isClosed_subset (isClosed_tsupport _) hsK
  have h := Localization.norm_oscillatory_integral_le_of_phase_derivative_bounds
    (μ := μ) hU e (R • F) a q (hF.const_smul R) ha hsU hc hδ hL0 hR0
    hscaledGap hscaledUpper hscaledProfile hamplitude
  change ‖∫ x, Localization.phaseOscillation (R • F) x * a x ∂μ‖ ≤
    (decayConstant e δ G P A q * (L ^ b * (L / R) ^ q)) * μ.real (tsupport a) at h
  calc
    _ ≤ (decayConstant e δ G P A q * (L ^ b * (L / R) ^ q)) *
        μ.real (tsupport a) := h
    _ ≤ (decayConstant e δ G P A q * (L ^ b * (L / R) ^ q)) * μ.real K := by
      apply mul_le_mul_of_nonneg_left (measureReal_mono hsK hK.measure_lt_top.ne)
      exact mul_nonneg (decayConstant_nonneg e δ G P A hA q)
        (mul_nonneg (pow_nonneg hL0 _) (pow_nonneg (div_nonneg hL0 hR0.le) _))
    _ = _ := by ring

end JanetCartan.FiniteChain.Retarded.HalfSpace
