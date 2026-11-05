module

public import JanetCartan.Analysis.ODE.PositiveTransport.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Time regularity of scalar transport

The time regularity part of `app:ch_waves:thm:leading`, on the original open
interval, hence on every compact subinterval. Joint parameter regularity is a
separate integral differentiation problem.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan

/-- `app:ch_waves:thm:leading`: a smooth time coefficient has a smooth primitive. -/
theorem contDiffOn_transportIntegral {c : ℝ → ℝ} {I : Set ℝ} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hc : ContDiffOn ℝ ∞ c I)
    (ht₀ : t₀ ∈ I) :
    ContDiffOn ℝ ∞ (fun t ↦ ∫ s in t₀..t, c s) I := by
  have hd (t) (ht : t ∈ I) := hasDerivAt_transportIntegral hI hIc hc.continuousOn ht₀ ht
  have h : ContDiffOn ℝ (∞ + 1) (fun t ↦ ∫ s in t₀..t, c s) I := by
    apply (contDiffOn_succ_iff_deriv_of_isOpen hI).mpr
    refine ⟨fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · simp
    · exact hc.congr (fun t ht ↦ (hd t ht).deriv)
  simpa using h

/-- `app:ch_waves:thm:leading`: the flow exponential is smooth in time. -/
theorem contDiffOn_transportFactor {c : ℝ → ℝ} {I : Set ℝ} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hc : ContDiffOn ℝ ∞ c I)
    (ht₀ : t₀ ∈ I) : ContDiffOn ℝ ∞ (transportFactor c t₀) I :=
  (contDiffOn_transportIntegral hI hIc hc ht₀).neg.exp

/-- `app:ch_waves:thm:leading`: the scalar solution is smooth in time. -/
theorem contDiffOn_scalarTransport {c : ℝ → ℝ} {I : Set ℝ} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hc : ContDiffOn ℝ ∞ c I)
    (ht₀ : t₀ ∈ I) (r : ℝ) : ContDiffOn ℝ ∞ (scalarTransport c t₀ r) I :=
  (contDiffOn_transportFactor hI hIc hc ht₀).mul contDiffOn_const

end JanetCartan
