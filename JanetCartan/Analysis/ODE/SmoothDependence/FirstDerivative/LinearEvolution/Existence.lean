module

public import JanetCartan.Analysis.ODE.SmoothDependence.FirstDerivative.LinearEvolution.CompactExistence
public import JanetCartan.Analysis.ODE.SmoothDependence.FirstDerivative.VariationError

/-!
# Linear evolution without a uniform coefficient bound

Compact-interval existence and uniqueness are patched to obtain evolution on
the original open interval in `app:ch_regular_base:lem:buffered-interpolation`
and `app:lem:common-hamilton-phase`.
-/

@[expose] public section

open Set Metric
open scoped Topology NNReal

namespace JanetCartan.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:lem:common-hamilton-phase`: continuous coefficients suffice for
uniqueness between any two times in their interval of definition. -/
theorem linearEvolution_eq_of_hasDerivAt_uIcc
    {A J H : ℝ → E →L[ℝ] E} {t₀ t : ℝ}
    (hA : ContinuousOn A (uIcc t₀ t))
    (hJ : ∀ τ ∈ uIcc t₀ t, HasDerivAt J ((A τ).comp (J τ)) τ)
    (hH : ∀ τ ∈ uIcc t₀ t, HasDerivAt H ((A τ).comp (H τ)) τ)
    (hinit : J t₀ = H t₀) : J t = H t := by
  obtain ⟨K, hK⟩ := isCompact_uIcc.exists_bound_of_continuousOn hA
  have h := norm_le_gronwallBound_of_hasDerivAt_uIcc
    (R := fun τ ↦ J τ - H τ) (R' := fun τ ↦ (A τ).comp (J τ - H τ))
    (δ := 0) (L := K) (ε := 0)
    (fun τ hτ ↦ by simpa only [ContinuousLinearMap.comp_sub, Pi.sub_def] using
      (hJ τ hτ).sub (hH τ hτ))
    (by simp [hinit]) (fun τ hτ ↦ by
      simpa only [add_zero] using ((A τ).opNorm_comp_le (J τ - H τ)).trans
        (mul_le_mul_of_nonneg_right (hK τ hτ) (norm_nonneg _)))
  simpa only [gronwallBound_ε0_δ0, norm_le_zero_iff, sub_eq_zero] using h

/-- `app:ch_regular_base:lem:buffered-interpolation`: uniqueness of linear
evolution on a convex time set, with only continuity of the coefficient. -/
theorem linearEvolution_unique {A J H : ℝ → E →L[ℝ] E} {s : Set ℝ} {t₀ : ℝ}
    (hs : Convex ℝ s) (ht₀ : t₀ ∈ s) (hA : ContinuousOn A s)
    (hJ : ∀ t ∈ s, HasDerivAt J ((A t).comp (J t)) t)
    (hH : ∀ t ∈ s, HasDerivAt H ((A t).comp (H t)) t)
    (hinit : J t₀ = H t₀) : EqOn J H s := by
  intro t ht
  have hsub : uIcc t₀ t ⊆ s := hs.ordConnected.uIcc_subset ht₀ ht
  exact linearEvolution_eq_of_hasDerivAt_uIcc (hA.mono hsub)
    (fun τ hτ ↦ hJ τ (hsub hτ)) (fun τ hτ ↦ hH τ (hsub hτ)) hinit

variable [CompleteSpace E]

/-- `app:lem:common-hamilton-phase`: operator-valued linear evolution on a
compact interval, without a short-time condition or an assumed coefficient bound. -/
theorem exists_linearEvolution_compact {A : ℝ → E →L[ℝ] E} {a b : ℝ}
    (t₀ : Icc a b) (J₀ : E →L[ℝ] E) (hA : ContinuousOn A (Icc a b)) :
    ∃ J : ℝ → E →L[ℝ] E, J t₀ = J₀ ∧ Continuous J ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt J ((A t).comp (J t)) (Icc a b) t := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  apply exists_solution_compact_of_lipschitzWith t₀ J₀ (K := ⟨max K 0, le_max_right _ _⟩)
  · exact (hA.comp continuousOn_fst (fun _ h ↦ h.1)).clm_comp continuousOn_snd
  · intro t ht
    have hlip := lipschitzWith_affine_variational (P := E) (A t) (0 : E →L[ℝ] E)
    simp only [add_zero] at hlip
    exact hlip.weaken (by exact_mod_cast (hK t ht).trans (le_max_left K 0))

/-- `app:ch_regular_base:lem:buffered-interpolation`: a continuous linear
coefficient admits a solution on the entire open interval. The initial operator
is arbitrary. Joint dependence on external parameters is treated separately. -/
theorem exists_linearEvolution_Ioo {A : ℝ → E →L[ℝ] E} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) (J₀ : E →L[ℝ] E) (hA : ContinuousOn A (Ioo a b)) :
    ∃ J : ℝ → E →L[ℝ] E, J t₀ = J₀ ∧
      ∀ t ∈ Ioo a b, HasDerivAt J ((A t).comp (J t)) t := by
  classical
  have hex (t : Ioo a b) : ∃ l u : ℝ, ∃ J : ℝ → E →L[ℝ] E,
      Icc l u ⊆ Ioo a b ∧ t₀ ∈ Ioo l u ∧ t.1 ∈ Ioo l u ∧ J t₀ = J₀ ∧
      ∀ τ ∈ Ioo l u, HasDerivAt J ((A τ).comp (J τ)) τ := by
    obtain ⟨l, hal, hl⟩ := exists_between (lt_min ht₀.1 t.2.1)
    obtain ⟨u, hu, hub⟩ := exists_between (max_lt ht₀.2 t.2.2)
    have hsub : Icc l u ⊆ Ioo a b := fun τ hτ ↦
      ⟨hal.trans_le hτ.1, hτ.2.trans_lt hub⟩
    have h₀ : t₀ ∈ Ioo l u := ⟨hl.trans_le (min_le_left _ _),
      (le_max_left _ _).trans_lt hu⟩
    obtain ⟨J, hinit, _, hd⟩ := exists_linearEvolution_compact
      ⟨t₀, Ioo_subset_Icc_self h₀⟩ J₀ (hA.mono hsub)
    exact ⟨l, u, J, hsub, h₀,
      ⟨hl.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hu⟩,
      hinit, fun τ hτ ↦ (hd τ (Ioo_subset_Icc_self hτ)).hasDerivAt
        (Icc_mem_nhds hτ.1 hτ.2)⟩
  choose l u j hsub h₀ ht hinit hd using hex
  have hcompat (r q : Ioo a b) : EqOn (j r) (j q) (Ioo (l r) (u r) ∩ Ioo (l q) (u q)) := by
    apply linearEvolution_unique ((convex_Ioo _ _).inter (convex_Ioo _ _))
      ⟨h₀ r, h₀ q⟩ (hA.mono (fun τ hτ ↦ hsub r (Ioo_subset_Icc_self hτ.1)))
      (fun τ hτ ↦ hd r τ hτ.1) (fun τ hτ ↦ hd q τ hτ.2)
    rw [hinit, hinit]
  let J : ℝ → E →L[ℝ] E := fun t ↦ if ht : t ∈ Ioo a b then j ⟨t, ht⟩ t else J₀
  have heq (q : Ioo a b) : EqOn J (j q) (Ioo (l q) (u q)) := by
    intro t htq
    have hta : t ∈ Ioo a b := hsub q (Ioo_subset_Icc_self htq)
    dsimp only [J]
    rw [dite_eq_left hta]
    exact hcompat ⟨t, hta⟩ q ⟨ht ⟨t, hta⟩, htq⟩
  refine ⟨J, ?_, ?_⟩
  · exact (heq ⟨t₀, ht₀⟩ (h₀ ⟨t₀, ht₀⟩)).trans (hinit _)
  · intro t hta
    let q : Ioo a b := ⟨t, hta⟩
    have hevent : J =ᶠ[𝓝 t] j q :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Ioo (l q) (u q), isOpen_Ioo.mem_nhds (ht q), heq q⟩
    rw [heq q (ht q)]
    exact (hd q t (ht q)).congr_of_eventuallyEq hevent

end JanetCartan.ODE
