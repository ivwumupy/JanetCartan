module

public import JanetCartan.Analysis.ODE.SmoothDependence.LocalExistence

/-!
# Constant parameters in local ODEs

For `app:lem:common-hamilton-phase`, parameters are included as state coordinates
with zero velocity. This section establishes continuous dependence; it does not
assert differentiability of the solution in these coordinates.
-/

@[expose] public section

open Metric Set
open scoped NNReal Topology

namespace JanetCartan.ODE

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `app:lem:common-hamilton-phase`: nearby parameters and initial values share one
local flow domain. Parameters remain constant along the lifted flow, and the
solution is continuous jointly in parameter, initial value, and time, with a
uniform Lipschitz bound in the first two variables. -/
theorem exists_parameterized_localFlow_in_open {V : P × E → E} {z₀ : P × E} {U : Set (P × E)}
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hV : ContDiffAt ℝ 1 V z₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : (P × E) × ℝ → E,
      ContinuousOn Φ (closedBall z₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)) ∧
      (∀ z ∈ closedBall z₀ r, Φ (z, t₀) = z.2) ∧
      (∀ z ∈ closedBall z₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt (fun s ↦ Φ (z, s)) (V (z.1, Φ (z, t))) t) ∧
      (∀ z ∈ closedBall z₀ r, ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
        (z.1, Φ (z, t)) ∈ U) ∧
      ∃ K : ℝ≥0, ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
        LipschitzOnWith K (fun z ↦ Φ (z, t)) (closedBall z₀ r) := by
  have hF : ContDiffAt ℝ 1 (fun z ↦ ((0 : P), V z)) z₀ :=
    contDiffAt_const.prodMk hV
  obtain ⟨r, hr, ε, hε, Ψ, hcont, hinit, hderiv, hrange, K, hlip⟩ :=
    exists_localFlow_in_open hU hz₀ hF t₀
  have htime : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hfst (z) (hz : z ∈ closedBall z₀ r) :
      EqOn (fun t ↦ (Ψ (z, t)).1) (fun _ ↦ z.1) (Icc (t₀ - ε) (t₀ + ε)) := by
    have hc : ContinuousOn (fun t ↦ Ψ (z, t)) (Icc (t₀ - ε) (t₀ + ε)) :=
      hcont.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht ↦ ⟨hz, ht⟩)
    refine ODE_solution_unique_of_mem_Icc
      (v := fun _ _ ↦ (0 : P)) (s := fun _ ↦ univ) (K := 0)
      (fun _ _ ↦ (LipschitzWith.const 0).lipschitzOnWith) htime hc.fst
      (fun t ht ↦ ?_) (fun _ _ ↦ mem_univ _) continuousOn_const
      (fun t _ ↦ hasDerivAt_const t z.1) (fun _ _ ↦ mem_univ _) ?_
    · exact (ContinuousLinearMap.fst ℝ P E).hasFDerivAt.comp_hasDerivAt t (hderiv z hz t ht)
    · exact congrArg Prod.fst (hinit z hz)
  refine ⟨r, hr, ε, hε, fun w ↦ (Ψ w).2, hcont.snd, ?_, ?_, ?_, K, ?_⟩
  · intro z hz
    exact congrArg Prod.snd (hinit z hz)
  · intro z hz t ht
    have hd := (ContinuousLinearMap.snd ℝ P E).hasFDerivAt.comp_hasDerivAt t (hderiv z hz t ht)
    change HasDerivAt (fun s ↦ (Ψ (z, s)).2) (V (Ψ (z, t))) t at hd
    convert hd using 1
    have he : (Ψ (z, t)).1 = z.1 := hfst z hz (Ioo_subset_Icc_self ht)
    rw [← he]
  · intro z hz t ht
    have he : (Ψ (z, t)).1 = z.1 := hfst z hz ht
    rw [← he]
    exact hrange z hz t ht
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    have hd : dist (Ψ (z, t)).2 (Ψ (w, t)).2 ≤ dist (Ψ (z, t)) (Ψ (w, t)) := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    exact hd.trans ((hlip t ht).dist_le_mul z hz w hw)

end JanetCartan.ODE
