module

public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Invariance of characteristic graphs

The differential argument in `app:ch_regular:thm:no-return`. A graph tangent to
the characteristic vector field contains every solution starting on it, for the
entire interval on which the base curve remains in the graph's domain. The
initial time may be either endpoint or an interior point.

This module does not construct the phase graphs. For a Hamilton field the
tangency identity is the differentiated eikonal equation; the Lipschitz bound
below is a local bound on the differentiated vector field.
-/

@[expose] public section

open Set
open scoped NNReal

namespace JanetCartan.ProtectedFlow

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Uniqueness on a complete closed segment in both orientations, allowing the
initial time at either endpoint (`app:ch_regular:thm:no-return`). -/
theorem solution_eqOn_of_initial_mem_Icc
    {v : ℝ → F → F} {D : ℝ → Set F} {K : ℝ≥0}
    {f g : ℝ → F} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b)
    (hv : ∀ t ∈ Icc a b, LipschitzOnWith K (v t) (D t))
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (v t (f t)) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (v t (g t)) t)
    (hfD : ∀ t ∈ Icc a b, f t ∈ D t)
    (hgD : ∀ t ∈ Icc a b, g t ∈ D t)
    (hinit : f t₀ = g t₀) : EqOn f g (Icc a b) := by
  have hfc : ContinuousOn f (Icc a b) := fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) := fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt
  have hleft : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
  have hright : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
  have hl := ODE_solution_unique_of_mem_Icc_left
    (fun t ht ↦ hv t (hleft (Ioc_subset_Icc_self ht)))
    (hfc.mono hleft)
    (fun t ht ↦ (hf t (hleft (Ioc_subset_Icc_self ht))).hasDerivWithinAt)
    (fun t ht ↦ hfD t (hleft (Ioc_subset_Icc_self ht)))
    (hgc.mono hleft)
    (fun t ht ↦ (hg t (hleft (Ioc_subset_Icc_self ht))).hasDerivWithinAt)
    (fun t ht ↦ hgD t (hleft (Ioc_subset_Icc_self ht))) hinit
  have hr := ODE_solution_unique_of_mem_Icc_right
    (fun t ht ↦ hv t (hright (Ico_subset_Icc_self ht)))
    (hfc.mono hright)
    (fun t ht ↦ (hf t (hright (Ico_subset_Icc_self ht))).hasDerivWithinAt)
    (fun t ht ↦ hfD t (hright (Ico_subset_Icc_self ht)))
    (hgc.mono hright)
    (fun t ht ↦ (hg t (hright (Ico_subset_Icc_self ht))).hasDerivWithinAt)
    (fun t ht ↦ hgD t (hright (Ico_subset_Icc_self ht))) hinit
  intro t ht
  rcases le_total t t₀ with h | h
  · exact hl ⟨ht.1, h⟩
  · exact hr ⟨h, ht.2⟩

/-- A tangent graph is preserved along an entire characteristic segment in
either orientation (`app:ch_regular:thm:no-return`). For Hamilton's equations,
`A = q_ξ`, `B = -q_x`, `g = dψ`, and `dg = ψ_xx`.

The physical-domain hypothesis is imposed at **every** time. The Lipschitz
condition is on `B - dg ∘ A` in the covector variable, on a region containing
both the actual covectors and the graph. No graph-invariance hypothesis is used.
-/
theorem characteristic_stays_on_graph
    {W : Set E} {D : Set F} {A : E → F → E} {B : E → F → F}
    {g : E → F} {dg : E → E →L[ℝ] F} {K : ℝ≥0}
    {x : ℝ → E} {p : ℝ → F} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b)
    (hgraph : ∀ y ∈ W, HasFDerivAt g (dg y) y)
    (htangent : ∀ y ∈ W, B y (g y) = dg y (A y (g y)))
    (hlip : ∀ y ∈ W, LipschitzOnWith K (fun z ↦ B y z - dg y (A y z)) D)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (A (x t) (p t)) t)
    (hp : ∀ t ∈ Icc a b, HasDerivAt p (B (x t) (p t)) t)
    (hxW : ∀ t ∈ Icc a b, x t ∈ W)
    (hpD : ∀ t ∈ Icc a b, p t ∈ D)
    (hgD : ∀ y ∈ W, g y ∈ D)
    (hinit : p t₀ = g (x t₀)) :
    ∀ t ∈ Icc a b, p t = g (x t) := by
  let v : ℝ → F → F := fun t z ↦
    B (x t) z - dg (x t) (A (x t) z) + dg (x t) (A (x t) (p t))
  apply solution_eqOn_of_initial_mem_Icc (v := v) (D := fun _ ↦ D) ht₀
      (K := K) _ _ _ hpD (fun t ht ↦ hgD (x t) (hxW t ht)) hinit
  · intro t ht z hz w hw
    simpa only [v, edist_add_right] using hlip (x t) (hxW t ht) hz hw
  · intro t ht
    simpa [v] using hp t ht
  · intro t ht
    have h := (hgraph (x t) (hxW t ht)).comp_hasDerivAt t (hx t ht)
    simpa [v, htangent (x t) (hxW t ht), Function.comp_def] using h

end JanetCartan.ProtectedFlow
