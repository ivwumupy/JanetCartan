module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Joint regularity from continuous partial derivatives

This is the final calculus step in the flow argument for
`app:lem:common-hamilton-phase`.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace JanetCartan.ODE

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `app:lem:common-hamilton-phase`: continuous spatial and time derivatives
give joint `C¹` regularity on an open product domain. -/
theorem contDiffOn_one_of_continuous_partials {Φ : E × ℝ → F}
    {A : E × ℝ → E →L[ℝ] F} {v : E × ℝ → F} {s : Set E} {I : Set ℝ}
    (hs : IsOpen s) (hI : IsOpen I)
    (hA : ContinuousOn A (s ×ˢ I)) (hv : ContinuousOn v (s ×ˢ I))
    (hdx : ∀ p ∈ s ×ˢ I, HasFDerivAt (fun y ↦ Φ (y, p.2)) (A p) p.1)
    (hdt : ∀ p ∈ s ×ˢ I, HasDerivAt (fun t ↦ Φ (p.1, t)) (v p) p.2) :
    ContDiffOn ℝ 1 Φ (s ×ˢ I) := by
  have hS : IsOpen (s ×ˢ I) := hs.prod hI
  let B : E × ℝ → ℝ →L[ℝ] F := fun p ↦ ContinuousLinearMap.toSpanSingleton ℝ (v p)
  have hB : ContinuousOn B (s ×ˢ I) :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := F)).continuous.comp_continuousOn hv
  have hd (p) (hp : p ∈ s ×ˢ I) : HasFDerivAt Φ ((A p).coprod (B p)) p := by
    have hx : ∀ᶠ q in 𝓝 p, HasFDerivAt (fun y ↦ Φ (y, q.2)) (A q) q.1 :=
      Filter.mem_of_superset (hS.mem_nhds hp) (fun q hq ↦ hdx q hq)
    have ht : ∀ᶠ q in 𝓝 p, HasFDerivAt (fun t ↦ Φ (q.1, t)) (B q) q.2 :=
      Filter.mem_of_superset (hS.mem_nhds hp) (fun q hq ↦ (hdt q hq).hasFDerivAt)
    exact (hasStrictFDerivAt_uncurry_coprod
      (f := fun x t ↦ Φ (x, t)) (f₁ := fun x t ↦ A (x, t))
      (f₂ := fun x t ↦ B (x, t)) hx ht
      ((hA p hp).continuousAt (hS.mem_nhds hp))
      ((hB p hp).continuousAt (hS.mem_nhds hp))).hasFDerivAt
  change ContDiffOn ℝ (0 + 1) Φ (s ×ˢ I)
  rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS.uniqueDiffOn]
  exact ⟨by simp, fun p ↦ (A p).coprod (B p),
    contDiffOn_zero.mpr (hA.continuousLinearMapCoprod hB),
    fun p hp ↦ (hd p hp).hasFDerivWithinAt⟩

end JanetCartan.ODE
