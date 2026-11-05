module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.SourceEstimates

/-!
# Removing a compact frequency cutoff

Absolute integrability and Fubini for the literal kernel in Step 1 of
`app:ch_osc:prop:osc-normal`. These lemmas connect the finite regularizations of
`app:ch_osc:lem:osc-amplitude` to the full frequency integral on L² inputs.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace JanetCartan.NormalComparison

open AmplitudeBound

variable {n : ℕ}
  (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)) → ℂ)
  (hb : StronglyMeasurable (Function.uncurry b)) {R A ρ : ℝ}
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ))
  (hzero : ∀ ξ z, ‖b ξ z‖ ≤ A)
  (hfreq : ∀ ξ, ξ ∉ Metric.closedBall 0 ρ → ∀ z, b ξ z = 0)

include hb hs hzero hfreq

omit hb hs hzero in
/-- The inner frequency integral of the literal kernel is absolutely
convergent at every pair of physical positions. This validates the full kernel
used by `exists_compactFrequencyMatrixAmplitudeOperator`
(`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem integrable_compactFrequencyAmplitude_frequency
    (hc : Continuous (Function.uncurry b))
    (x y : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun ξ ↦
      Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
        b ξ (pairedPosition x y)) := by
  have hbc : Continuous (fun ξ ↦ b ξ (pairedPosition x y)) :=
    hc.comp (continuous_id.prodMk continuous_const)
  have hc' : Continuous (fun ξ ↦
      Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
        b ξ (pairedPosition x y)) := by fun_prop
  apply hc'.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 ρ)
  intro ξ hξ
  by_contra hout
  exact hξ (by simp [hfreq ξ hout])

/-- Compact frequency support upgrades the existing restricted product
integrability estimate to full product volume. This justifies the full-kernel
Fubini step consumed by `exists_compactFrequencyMatrixAmplitudeOperator`
(`app:ch_osc:lem:osc-amplitude`, `app:ch_osc:prop:osc-normal`, Step 1). -/
theorem integrable_compactFrequencyAmplitude_prod
    (f : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
      Complex.exp (↑(2 * Real.pi * ⟪x - p.2, p.1⟫) * Complex.I) *
        b p.1 (pairedPosition x p.2) * f p.2) (volume.prod volume) := by
  have hi := integrable_boxScalarAmplitudeKernel_prod b hb (amplitudeBoxScale_pos R)
    (div_amplitudeBoxScale_lt R) hs A hzero ρ f x
  rw [Measure.restrict_prod_eq_prod_univ] at hi
  apply (integrableOn_iff_integrable_of_support_subset (s :=
    Metric.closedBall 0 ρ ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n)))) ?_).mp hi
  intro p hp
  refine ⟨?_, mem_univ _⟩
  by_contra hout
  exact hp (by simp [hfreq p.1 hout])

/-- Once the frequency ball contains the carrier, its finite regularization
is exactly the literal full kernel, with frequency integrated first. The
physical/frequency exchange is justified for every L² input by absolute product
integrability (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem boxScalarAmplitudeKernel_eq_full_of_frequency_support
    (f : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2)
    (x : EuclideanSpace ℝ (Fin n)) :
    boxScalarAmplitudeKernel b ρ f x = ∫ y,
      (∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
        b ξ (pairedPosition x y)) * f y := by
  unfold boxScalarAmplitudeKernel
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun ξ hξ ↦ by
    simp [hfreq ξ hξ])]
  rw [integral_integral_swap (integrable_compactFrequencyAmplitude_prod
    b hb hs hzero hfreq f x)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ integral_mul_const (f y) _)

/-- Absolute convergence of the physical integral in the full kernel action,
as used by `exists_compactFrequencyMatrixAmplitudeOperator`
(`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem integrable_compactFrequencyAmplitude_action
    (f : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦
      (∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
        b ξ (pairedPosition x y)) * f y) := by
  have hi := (integrable_compactFrequencyAmplitude_prod b hb hs hzero hfreq f x).integral_prod_right
  simpa only [integral_mul_const] using hi

end JanetCartan.NormalComparison
