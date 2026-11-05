module

public import JanetCartan.Analysis.Sobolev.Local.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Compatibility of local Sobolev representatives

The all-order regularity argument for `app:not:fourier` and
`app:ch_regular:thm:exact-correction` must allow different extensions at different
orders. Continuous representatives of the same local L² class agree on the open
domain. Consequently, finite-order representatives, once constructed, give one
smooth representative. This module proves that compatibility step; it does not
assert the Sobolev embedding that constructs the finite-order representatives.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set (EuclideanSpace ℝ (Fin n))}

/-- For `app:not:fourier`, a continuous representative inherits finite-order
regularity from any almost-everywhere equal representative on the open domain. -/
theorem contDiffOn_of_ae_eq {f g : EuclideanSpace ℝ (Fin n) → F}
    {k : ℕ∞ω} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hg : ContDiffOn ℝ k g U) (hfg : f =ᵐ[volume.restrict U] g) :
    ContDiffOn ℝ k f U := by
  exact hg.congr (Measure.eqOn_open_of_ae_eq hfg hU hf hg.continuousOn)

/-- The compatibility step in the `H^∞` regularity assertion of
`app:not:fourier`, used in `app:ch_regular:thm:exact-correction`: finite-order
representatives of one local L² class yield a single smooth representative.
The finite-order representatives may be chosen independently at each order. -/
theorem exists_contDiffOn_infty_ae_eq_of_finiteOrderRepresentatives
    (hU : IsOpen U) (u : LocalL2 U F)
    (hu : ∀ k : ℕ, ∃ f : EuclideanSpace ℝ (Fin n) → F,
      ContDiffOn ℝ k f U ∧ f =ᵐ[volume.restrict U] u) :
    ∃ f : EuclideanSpace ℝ (Fin n) → F,
      ContDiffOn ℝ ∞ f U ∧ f =ᵐ[volume.restrict U] u := by
  obtain ⟨f, hf, hfu⟩ := hu 0
  refine ⟨f, contDiffOn_infty.mpr ?_, hfu⟩
  intro k
  obtain ⟨g, hg, hgu⟩ := hu k
  exact contDiffOn_of_ae_eq hU hf.continuousOn hg (hfu.trans hgu.symm)

end JanetCartan.LocalSobolev
