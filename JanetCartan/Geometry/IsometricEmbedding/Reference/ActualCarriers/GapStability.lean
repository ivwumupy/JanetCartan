module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Order.Compact

import Mathlib.Tactic.Linarith

/-!
# Persistence of simple characteristic zeros

The compactness argument in Step 2 of `app:ch_seed:prop:seed-actual-menu`.
Closeness is required for both the polynomial and its derivative: a perturbed
zero need not lie in the reference zero set.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ActualCarriers

variable {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V]

/-- On a compact set without common zeros of a scalar and a vector-valued map,
all sufficiently close pairs have a uniform vector gap at scalar zeros
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem exists_simple_zero_perturbation_gap {K : Set X} (hK : IsCompact K)
    {p : X → ℝ} {D : X → V} (hp : ContinuousOn p K) (hD : ContinuousOn D K)
    (hsimple : ∀ x ∈ K, p x = 0 → D x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p' : X → ℝ) (D' : X → V),
      (∀ x ∈ K, ‖p' x - p x‖ ≤ c) →
      (∀ x ∈ K, ‖D' x - D x‖ ≤ c) →
      ∀ x ∈ K, p' x = 0 → c ≤ ‖D' x‖ := by
  have hpos : ∀ x ∈ K, 0 < ‖p x‖ + ‖D x‖ := by
    intro x hx
    by_cases hz : p x = 0
    · simpa [hz] using norm_pos_iff.mpr (hsimple x hx hz)
    · exact add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hz) (norm_nonneg _)
  obtain ⟨a, ha, hgap⟩ := hK.exists_forall_le' (hp.norm.add hD.norm) hpos
  refine ⟨a / 3, by linarith, ?_⟩
  intro p' D' hp' hD' x hx hz
  have hpbound : ‖p x‖ ≤ a / 3 := by simpa [hz] using hp' x hx
  have htriangle : ‖D x‖ ≤ ‖D' x‖ + a / 3 := by
    calc
      ‖D x‖ ≤ ‖D' x‖ + ‖D x - D' x‖ := norm_le_insert' _ _
      _ ≤ ‖D' x‖ + a / 3 :=
        add_le_add (le_refl _) (by simpa [norm_sub_rev] using hD' x hx)
  have hgap' : a ≤ ‖p x‖ + ‖D x‖ := hgap x hx
  linarith

/-- Uniform `C¹` perturbations preserve a positive differential norm at every
actual zero on a fixed compact angular set
(`app:ch_seed:prop:seed-actual-menu`, Step 2). No differentiability or continuity
of the perturbation is needed beyond the stated bounds on its actual `fderiv`. -/
theorem exists_fderiv_zero_perturbation_gap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) {p : E → ℝ}
    (hp : ContinuousOn p K) (hD : ContinuousOn (fderiv ℝ p) K)
    (hsimple : ∀ ξ ∈ K, p ξ = 0 → fderiv ℝ p ξ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ p' : E → ℝ,
      (∀ ξ ∈ K, ‖p' ξ - p ξ‖ ≤ c) →
      (∀ ξ ∈ K, ‖fderiv ℝ p' ξ - fderiv ℝ p ξ‖ ≤ c) →
      ∀ ξ ∈ K, p' ξ = 0 → c ≤ ‖fderiv ℝ p' ξ‖ := by
  obtain ⟨c, hc, h⟩ := exists_simple_zero_perturbation_gap (D := fderiv ℝ p) hK hp hD hsimple
  exact ⟨c, hc, fun p' ↦ h p' (fderiv ℝ p')⟩

end JanetCartan.ActualCarriers
