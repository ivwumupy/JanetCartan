module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Original-input energy for sharp row multiplication

The weighted Fourier-column estimate of `app:ch_osc:eq:amplitude-row`
uses only the original amplitude's row energy. Finite sums are integrated
against the original `|f|²`, so this argument applies to an arbitrary
source measure without a sigma-finiteness assumption. Its actual source
producer is the compact-row Sobolev-to-Fourier coefficient estimate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.AmplitudeBound.PaperEstimates

variable {κ X : Type*} [Countable κ] [MeasurableSpace X] {μ : Measure X}

private theorem integral_norm_sq_Lp (f : Lp ℂ 2 μ) :
    (∫ u, ‖f u‖ ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) f f).symm

/-- Integrating the finite original row-energy inequality gives the
actual squared `L²` coefficient-input bound. No source derivatives or
product-measure Fubini premise occur
(`app:ch_osc:eq:amplitude-row`). -/
theorem sum_weighted_multiplier_sq_le
    (w : κ → ℝ) (a : κ → Lp ℂ ∞ μ) (B : ℝ)
    (hrow : ∀ s : Finset κ, ∀ᵐ u ∂μ, ∑ k ∈ s, w k * ‖a k u‖ ^ 2 ≤ B ^ 2)
    (s : Finset κ) (f : Lp ℂ 2 μ) :
    (∑ k ∈ s, w k * ‖multiplicationOperator (a k) f‖ ^ 2) ≤ B ^ 2 * ‖f‖ ^ 2 := by
  have hi k : Integrable (fun u ↦ w k * ‖multiplicationOperator (a k) f u‖ ^ 2) μ :=
    ((Lp.memLp (multiplicationOperator (a k) f)).integrable_norm_pow (by decide)).const_mul _
  have hfint : Integrable (fun u ↦ B ^ 2 * ‖f u‖ ^ 2) μ :=
    ((Lp.memLp f).integrable_norm_pow (by decide)).const_mul _
  have hmult : ∀ᵐ u ∂μ, ∀ k, multiplicationOperator (a k) f u = a k u * f u :=
    ae_all_iff.mpr (fun k ↦ multiplicationOperator_coeFn (a k) f)
  calc
    _ = ∑ k ∈ s, ∫ u, w k * ‖multiplicationOperator (a k) f u‖ ^ 2 ∂μ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_const_mul, integral_norm_sq_Lp]
    _ = ∫ u, ∑ k ∈ s, w k * ‖multiplicationOperator (a k) f u‖ ^ 2 ∂μ :=
      (integral_finsetSum s (fun k _ ↦ hi k)).symm
    _ ≤ ∫ u, B ^ 2 * ‖f u‖ ^ 2 ∂μ := by
      apply integral_mono_ae (integrable_finsetSum s (fun k _ ↦ hi k)) hfint
      filter_upwards [hrow s, hmult] with u hu hm
      simp_rw [hm, norm_mul, mul_pow, ← mul_assoc]
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hu (sq_nonneg _)
    _ = _ := by rw [integral_const_mul, integral_norm_sq_Lp]

/-- The original bounded operator transports the actual weighted
coefficient energy with precisely its squared operator norm. This
supplies the input to the Hilbert-valued Sobolev diagonal construction
in `app:ch_osc:eq:amplitude-row`. -/
theorem transformed_row_energy
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (a : κ → Lp ℂ ∞ μ) (B : ℝ)
    (hrow : ∀ s : Finset κ, ∀ᵐ u ∂μ, ∑ k ∈ s, w k * ‖a k u‖ ^ 2 ≤ B ^ 2)
    (T : Lp ℂ 2 μ →L[ℂ] H) (f : Lp ℂ 2 μ) :
    Summable (fun k ↦ w k * ‖T (multiplicationOperator (a k) f)‖ ^ 2) ∧
      (∑' k, w k * ‖T (multiplicationOperator (a k) f)‖ ^ 2) ≤
        ‖T‖ ^ 2 * B ^ 2 * ‖f‖ ^ 2 := by
  have hnonneg k : 0 ≤ w k * ‖T (multiplicationOperator (a k) f)‖ ^ 2 :=
    mul_nonneg (hw k) (sq_nonneg _)
  have hfinite (s : Finset κ) :
      (∑ k ∈ s, w k * ‖T (multiplicationOperator (a k) f)‖ ^ 2) ≤
        ‖T‖ ^ 2 * B ^ 2 * ‖f‖ ^ 2 := by
    calc
      _ ≤ ∑ k ∈ s, w k * (‖T‖ ^ 2 * ‖multiplicationOperator (a k) f‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_left _ (hw k)
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
          (T.le_opNorm (multiplicationOperator (a k) f)) 2
      _ = ‖T‖ ^ 2 * ∑ k ∈ s, w k * ‖multiplicationOperator (a k) f‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ ≤ ‖T‖ ^ 2 * (B ^ 2 * ‖f‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_weighted_multiplier_sq_le w a B hrow s f) (sq_nonneg _)
      _ = _ := by ring
  exact ⟨summable_of_sum_le hnonneg hfinite, Real.tsum_le_of_sum_le hnonneg hfinite⟩

end JanetCartan.AmplitudeBound.PaperEstimates
