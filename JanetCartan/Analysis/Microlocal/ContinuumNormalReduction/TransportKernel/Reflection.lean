module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Substitution
public import JanetCartan.Analysis.Operator.RealQuadratures

/-!
# Reflected real amplitudes

The frequency reflection needed after the checked real-quadrature identity
`realQuadratureChannel_normal_eq_four_realPart`, for
`app:ch_background:eq:bg-real-symbol`. The input remains the entire complex
Hilbert space considered over the reals. No even angular mask is used.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace JanetCartan.ContinuumRow.TransportKernel

variable {n : ℕ}

private theorem conjugate_phase (θ : ℝ) :
    conj (NormalComparison.oscillatoryFactor 1 θ) =
      NormalComparison.oscillatoryFactor 1 (-θ) := by
  simp only [NormalComparison.oscillatoryFactor, one_mul, ← Complex.exp_conj,
    map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  congr 1
  ring

/-- Reflection of a real amplitude conjugates its literal oscillatory integral.
This is a Lebesgue frequency substitution, without any evenness assumption
(`app:ch_background:eq:bg-real-symbol`). -/
theorem integral_reflected_amplitude (a : Euclidean n → ℝ) (z : Euclidean n) :
    (∫ k, NormalComparison.oscillatoryFactor 1 (inner ℝ z k) * (a (-k) : ℂ)) =
      conj (∫ k, NormalComparison.oscillatoryFactor 1 (inner ℝ z k) * (a k : ℂ)) := by
  rw [← integral_neg_eq_self (fun k ↦
    NormalComparison.oscillatoryFactor 1 (inner ℝ z k) * (a (-k) : ℂ)) volume,
    ← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro k
  simp only [neg_neg, inner_neg_right, map_mul, Complex.conj_ofReal, conjugate_phase]

/-- Integrability of the reflected integrand follows from the original one;
no extra analytic estimate is lost by reflection
(`app:ch_background:eq:bg-real-symbol`). -/
theorem integrable_reflected_amplitude (a : Euclidean n → ℝ) (z : Euclidean n)
    (ha : Integrable (fun k ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ z k) * (a k : ℂ))) :
    Integrable (fun k ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ z k) * (a (-k) : ℂ)) := by
  have hneg := (Measure.measurePreserving_neg (volume : Measure (Euclidean n))).integrable_comp_of_integrable ha
  have hc := (RCLike.conjLIE (K := ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hneg
  change Integrable (fun k ↦ conj
    (NormalComparison.oscillatoryFactor 1 (inner ℝ z (-k)) * (a (-k) : ℂ))) at hc
  simpa only [map_mul, Complex.conj_ofReal, conjugate_phase, inner_neg_right, neg_neg] using hc

/-- Combining the factor four from real quadratures with frequency reflection
produces `2 (a(k)+a(-k))`, not `4 a(k)`
(`app:ch_background:eq:bg-real-symbol`). The normalized PDO amplitude consequently
has factor `2 (2π)^n`. -/
theorem integral_reflected_eq_four_realPart (a : Euclidean n → ℝ) (z : Euclidean n)
    (ha : Integrable (fun k ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ z k) * (a k : ℂ))) :
    (∫ k, NormalComparison.oscillatoryFactor 1 (inner ℝ z k) *
      ((2 * (a k + a (-k)) : ℝ) : ℂ)) =
        ((4 * (∫ k, NormalComparison.oscillatoryFactor 1 (inner ℝ z k) *
          (a k : ℂ)).re : ℝ) : ℂ) := by
  have he : (fun k ↦ NormalComparison.oscillatoryFactor 1 (inner ℝ z k) *
      ((2 * (a k + a (-k)) : ℝ) : ℂ)) =
      fun k ↦ (2 : ℂ) *
        (NormalComparison.oscillatoryFactor 1 (inner ℝ z k) * (a k : ℂ) +
          NormalComparison.oscillatoryFactor 1 (inner ℝ z k) * (a (-k) : ℂ)) := by
    funext k
    push_cast
    ring
  rw [he, integral_const_mul, integral_add ha (integrable_reflected_amplitude a z ha),
    integral_reflected_amplitude, Complex.add_conj]
  push_cast
  ring

end JanetCartan.ContinuumRow.TransportKernel
