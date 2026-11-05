module

public import JanetCartan.Analysis.Microlocal.Localization.IntegrationByParts

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The actual phase operator

The coefficients of the nonstationary operator in
`app:ch_osc:prop:osc-source-shell`. Apply these definitions to the entire phase
`ψ(x)=ρ φ(x)-⟨x,ξ⟩`. In an orthonormal coordinate basis the denominator is
the square of the norm of that phase's gradient.
-/

@[expose] public noncomputable section

namespace JanetCartan.Localization

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- `app:ch_osc:prop:osc-source-shell`: the oscillation for the full Fourier
phase, including its signed frequency. -/
def phaseOscillation (ψ : E → ℝ) (x : E) : ℂ := Complex.exp ((ψ x : ℂ) * Complex.I)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `app:ch_osc:prop:osc-source-shell`: a real phase has unit modulus. -/
theorem norm_phaseOscillation (ψ : E → ℝ) (x : E) : ‖phaseOscillation ψ x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- `app:ch_osc:prop:osc-source-shell`: the exact derivative of the oscillation. -/
theorem fderiv_phaseOscillation (ψ : E → ℝ) {x : E}
    (hψ : DifferentiableAt ℝ ψ x) (v : E) :
    fderiv ℝ (phaseOscillation ψ) x v =
      phaseOscillation ψ x * ((fderiv ℝ ψ x v : ℝ) : ℂ) * Complex.I := by
  have h := ((Complex.ofRealCLM.hasFDerivAt.comp x hψ.hasFDerivAt).mul_const
    Complex.I).cexp
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at h
  unfold phaseOscillation
  rw [h.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  ac_rfl

/-- `app:ch_osc:prop:osc-source-shell`: sum of squared directional derivatives;
for an orthonormal basis this is the squared gradient norm. -/
def phaseGradientSquare (e : ι → E) (ψ : E → ℝ) (x : E) : ℝ :=
  ∑ i, (fderiv ℝ ψ x (e i)) ^ 2

/-- `app:ch_osc:prop:osc-source-shell`: the coefficient
`D_i ψ / (i |dψ|²)` of the integration-by-parts operator. -/
def phaseCoefficient (e : ι → E) (ψ : E → ℝ) (i : ι) (x : E) : ℂ :=
  (fderiv ℝ ψ x (e i) : ℝ) / (Complex.I * (phaseGradientSquare e ψ x : ℂ))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Algebraic normalization of the nonstationary coefficients in
`app:ch_osc:prop:osc-source-shell`. -/
theorem sum_phase_coefficients_mul_slopes (s : ι → ℝ) (h : (∑ i, s i ^ 2) ≠ 0) :
    ∑ i, (((s i : ℂ) / (Complex.I * ((∑ j, s j ^ 2 : ℝ) : ℂ))) *
      (s i : ℂ) * Complex.I) = 1 := by
  have hd : (((∑ j, s j ^ 2 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast h
  have hterm (i : ι) : ((s i : ℂ) / (Complex.I * ((∑ j, s j ^ 2 : ℝ) : ℂ))) *
      (s i : ℂ) * Complex.I = (s i : ℂ) ^ 2 / ((∑ j, s j ^ 2 : ℝ) : ℂ) := by
    field_simp
  simp_rw [hterm]
  rw [← Finset.sum_div]
  push_cast
  exact div_self (by simpa using hd)

/-- `app:ch_osc:prop:osc-source-shell`: the actual phase coefficients send
the oscillation to itself wherever the phase gradient is nonzero. -/
theorem phaseCoefficient_normalizes (e : ι → E) (ψ : E → ℝ) {x : E}
    (hψ : DifferentiableAt ℝ ψ x) (hgap : phaseGradientSquare e ψ x ≠ 0) :
    ∑ i, phaseCoefficient e ψ i x * fderiv ℝ (phaseOscillation ψ) x (e i) =
      phaseOscillation ψ x := by
  simp_rw [fderiv_phaseOscillation ψ hψ]
  calc
    (∑ i, phaseCoefficient e ψ i x *
        (phaseOscillation ψ x * (fderiv ℝ ψ x (e i) : ℝ) * Complex.I)) =
        phaseOscillation ψ x * ∑ i, (phaseCoefficient e ψ i x *
          (fderiv ℝ ψ x (e i) : ℝ) * Complex.I) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ac_rfl
    _ = phaseOscillation ψ x := by
      rw [show (∑ i, phaseCoefficient e ψ i x *
          (fderiv ℝ ψ x (e i) : ℝ) * Complex.I) = 1 from
        sum_phase_coefficients_mul_slopes _ hgap, mul_one]

open MeasureTheory

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- `app:ch_osc:prop:osc-source-shell`: repeated integration by parts with the
actual nonstationary coefficients. The only phase gap is on the original
amplitude support. Integrability and differentiability of the transposed
products remain explicit inputs; the quantitative derivative estimates and the
Sobolev shell conclusion are not asserted by this theorem. -/
theorem norm_oscillatory_integral_le_iterate_transposeAmplitude
    (e : ι → E) (ψ : E → ℝ) (a : E → ℂ) (q : ℕ)
    (hψ : Differentiable ℝ ψ)
    (hgap : ∀ x ∈ tsupport a, phaseGradientSquare e ψ x ≠ 0)
    (hleft : ∀ k < q, ∀ i, Integrable
      (fun x ↦ fderiv ℝ
        (fun y ↦ phaseCoefficient e ψ i y *
          ((transposeAmplitude e (phaseCoefficient e ψ))^[k] a) y)
        x (e i) * phaseOscillation ψ x) μ)
    (hright : ∀ k < q, ∀ i, Integrable
      (fun x ↦ (phaseCoefficient e ψ i x *
        ((transposeAmplitude e (phaseCoefficient e ψ))^[k] a) x) *
        fderiv ℝ (phaseOscillation ψ) x (e i)) μ)
    (hprod : ∀ k < q, ∀ i, Integrable
      (fun x ↦ (phaseCoefficient e ψ i x *
        ((transposeAmplitude e (phaseCoefficient e ψ))^[k] a) x) * phaseOscillation ψ x) μ)
    (hba : ∀ k < q, ∀ i x, x ∈ tsupport (phaseOscillation ψ) → DifferentiableAt ℝ
      (fun y ↦ phaseCoefficient e ψ i y *
        ((transposeAmplitude e (phaseCoefficient e ψ))^[k] a) y) x)
    (hfinal : Integrable ((transposeAmplitude e (phaseCoefficient e ψ))^[q] a) μ) :
    ‖∫ x, phaseOscillation ψ x * a x ∂μ‖ ≤
      ∫ x, ‖((transposeAmplitude e (phaseCoefficient e ψ))^[q] a) x‖ ∂μ := by
  apply norm_integral_le_integral_norm_iterate_transposeAmplitude e
    (phaseCoefficient e ψ) (phaseOscillation ψ) a q ?_ hleft hright hprod hba ?_ ?_ hfinal
  · intro k _ x hx
    apply phaseCoefficient_normalizes e ψ (hψ x)
    exact hgap x (tsupport_iterate_transposeAmplitude_subset e (phaseCoefficient e ψ) a k
      (subset_tsupport _ hx))
  · intro _ _ _ x _
    exact (((Complex.ofRealCLM.hasFDerivAt.comp x (hψ x).hasFDerivAt).mul_const
      Complex.I).cexp).differentiableAt
  · intro x
    exact (norm_phaseOscillation ψ x).le

end JanetCartan.Localization
