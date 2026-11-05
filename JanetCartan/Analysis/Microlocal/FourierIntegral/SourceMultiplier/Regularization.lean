module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Frequency regularization of the exact source symbol

The cutoff is applied at the original covector `η + v`, not at `v` or `η`.
This is the literal symbol corresponding to regularizing `A` before the source
multiplication in `app:ch_regular_base:eq:fixed-source-multiplication`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Matrix.Norms.Frobenius Topology RealInnerProductSpace
namespace JanetCartan.FourierIntegral

attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace

/-- Literal frequency regularization of the source symbol converges to the
untruncated symbol in `app:ch_regular_base:eq:fixed-source-multiplication`.
Compact frequency cutoffs may be supplied as `χ`; only their continuity,
uniform bound and convergence are needed for this limit. -/
theorem sourceSymbol_tendsto_frequencyCutoff {n r : ℕ}
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (x η : Euclidean n)
    (hS : Continuous (S x)) (hA : Continuous (A x)) (C : ℝ) (k : ℕ)
    (hbound : ∀ v, ‖A x (η + v)‖ ≤ C * (1 + ‖v‖ ^ k))
    (χ : ℕ → Euclidean n → ℂ) (hχ : ∀ j, Continuous (χ j))
    (hχbound : ∀ j ξ, ‖χ j ξ‖ ≤ 1)
    (hχlim : ∀ ξ, Tendsto (fun j ↦ χ j ξ) atTop (𝓝 1)) :
    Tendsto (fun j ↦ sourceSymbol S (fun z ξ ↦ χ j ξ • A z ξ) m x η)
      atTop (𝓝 (sourceSymbol S A m x η)) := by
  have he (j : ℕ) (v : Euclidean n) :
      sourceSymbolIntegrand S (fun z ξ ↦ χ j ξ • A z ξ) m x η v =
        χ j (η + v) • sourceSymbolIntegrand S A m x η v := by
    unfold sourceSymbolIntegrand
    exact smul_comm _ _ _
  unfold sourceSymbol
  simp_rw [he]
  apply tendsto_integral_of_dominated_convergence
    (fun v ↦ ‖sourceSymbolIntegrand S A m x η v‖)
  · intro j
    exact (by unfold sourceSymbolIntegrand; fun_prop : Continuous
      (fun v ↦ χ j (η + v) • sourceSymbolIntegrand S A m x η v)).aestronglyMeasurable
  · exact (sourceSymbolIntegrand_integrable S A m x η hS hA C k hbound).norm
  · intro j
    filter_upwards [] with v
    simpa only [norm_smul, one_mul] using
      mul_le_mul_of_nonneg_right (hχbound j (η + v))
        (norm_nonneg (sourceSymbolIntegrand S A m x η v))
  · filter_upwards [] with v
    simpa only [one_smul] using! (hχlim (η + v)).smul_const
      (sourceSymbolIntegrand S A m x η v)

end JanetCartan.FourierIntegral
