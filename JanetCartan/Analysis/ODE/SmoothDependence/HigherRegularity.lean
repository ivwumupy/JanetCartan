module

public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The calculus step for higher joint regularity

For `app:ch_regular_base:lem:buffered-interpolation`, regularity of the spatial
variational solution and of the time derivative gives one more joint derivative.
This module proves this calculus step; regularity of the variational solution
itself is a separate analytic input.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace JanetCartan.ODE

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `app:ch_regular_base:lem:buffered-interpolation`: `Cⁿ` spatial and time
partials give joint `Cⁿ⁺¹` regularity on an open product domain. This is a
calculus statement and does not assert regularity of a flow's variational
solution without proof. -/
theorem contDiffOn_succ_of_contDiffOn_partials {n : ℕ} {Φ : E × ℝ → F}
    {A : E × ℝ → E →L[ℝ] F} {v : E × ℝ → F} {s : Set E} {I : Set ℝ}
    (hs : IsOpen s) (hI : IsOpen I)
    (hA : ContDiffOn ℝ n A (s ×ˢ I)) (hv : ContDiffOn ℝ n v (s ×ˢ I))
    (hdx : ∀ p ∈ s ×ˢ I, HasFDerivAt (fun y ↦ Φ (y, p.2)) (A p) p.1)
    (hdt : ∀ p ∈ s ×ˢ I, HasDerivAt (fun t ↦ Φ (p.1, t)) (v p) p.2) :
    ContDiffOn ℝ (n + 1) Φ (s ×ˢ I) := by
  have hS : IsOpen (s ×ˢ I) := hs.prod hI
  let B : E × ℝ → ℝ →L[ℝ] F := fun p ↦ ContinuousLinearMap.toSpanSingleton ℝ (v p)
  have hB : ContDiffOn ℝ n B (s ×ˢ I) :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := F)).contDiff.comp_contDiffOn hv
  have hd (p) (hp : p ∈ s ×ˢ I) : HasFDerivAt Φ ((A p).coprod (B p)) p := by
    have hx : ∀ᶠ q in 𝓝 p, HasFDerivAt (fun y ↦ Φ (y, q.2)) (A q) q.1 :=
      Filter.mem_of_superset (hS.mem_nhds hp) (fun q hq ↦ hdx q hq)
    have ht : ∀ᶠ q in 𝓝 p, HasFDerivAt (fun t ↦ Φ (q.1, t)) (B q) q.2 :=
      Filter.mem_of_superset (hS.mem_nhds hp) (fun q hq ↦ (hdt q hq).hasFDerivAt)
    exact (hasStrictFDerivAt_uncurry_coprod
      (f := fun x t ↦ Φ (x, t)) (f₁ := fun x t ↦ A (x, t))
      (f₂ := fun x t ↦ B (x, t)) hx ht
      ((hA.continuousOn p hp).continuousAt (hS.mem_nhds hp))
      ((hB.continuousOn p hp).continuousAt (hS.mem_nhds hp))).hasFDerivAt
  have hAB : ContDiffOn ℝ n (fun p ↦ (A p).coprod (B p)) (s ×ˢ I) := by
    have h := (hA.clm_comp (contDiffOn_const (c := ContinuousLinearMap.fst ℝ E ℝ))).add
      (hB.clm_comp (contDiffOn_const (c := ContinuousLinearMap.snd ℝ E ℝ)))
    convert h using 1
    funext p
    exact ContinuousLinearMap.ext (fun w ↦ rfl)
  rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS.uniqueDiffOn]
  exact ⟨by simp, fun p ↦ (A p).coprod (B p), hAB,
    fun p hp ↦ (hd p hp).hasFDerivWithinAt⟩

end JanetCartan.ODE
