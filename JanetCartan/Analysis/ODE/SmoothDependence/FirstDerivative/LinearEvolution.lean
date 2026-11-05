module

public import JanetCartan.Analysis.ODE.SmoothDependence.FirstDerivative.LinearEvolution.Continuity

/-!
# Jointly continuous linear evolution on an open time interval

This supplies the continuous variational solution needed for the flow arguments
in `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`. Only continuity of the coefficient is required;
the time interval is preserved in full.
-/

@[expose] public section

open Set Metric Filter
open scoped Topology

namespace JanetCartan.ODE

variable {P E : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:lem:common-hamilton-phase`: compact-uniform parameter dependence
implies joint continuity throughout the open time interval. -/
theorem continuousOn_linearEvolution_univ
    {A J : P × ℝ → E →L[ℝ] E} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hA : ContinuousOn A (univ ×ˢ Ioo a b))
    (hJ : ∀ p t, t ∈ Ioo a b →
      HasDerivAt (fun τ ↦ J (p, τ)) ((A (p, t)).comp (J (p, t))) t)
    (hinit : ∀ p q, J (p, t₀) = J (q, t₀)) :
    ContinuousOn J (univ ×ˢ Ioo a b) := by
  intro z hz
  obtain ⟨l, hal, hl⟩ := exists_between (lt_min ht₀.1 hz.2.1)
  obtain ⟨u, hu, hub⟩ := exists_between (max_lt ht₀.2 hz.2.2)
  have hsub : Icc l u ⊆ Ioo a b := fun τ hτ ↦
    ⟨hal.trans_le hτ.1, hτ.2.trans_lt hub⟩
  have h₀ : t₀ ∈ Icc l u := ⟨(hl.trans_le (min_le_left _ _)).le,
    ((le_max_left _ _).trans_lt hu).le⟩
  have ht : z.2 ∈ Ioo l u := ⟨hl.trans_le (min_le_right _ _),
    (le_max_right _ _).trans_lt hu⟩
  let Jc : P → C(Icc l u, E →L[ℝ] E) := fun p ↦
    ⟨fun t ↦ J (p, t), continuousOn_iff_continuous_domRestrict.mp
      (HasDerivAt.continuousOn (fun t ht ↦ hJ p t (hsub ht)))⟩
  have hc : Continuous Jc := continuous_linearEvolution_compact h₀
    (hA.mono (prod_subset_prod_right hsub)) (fun p t ht ↦ hJ p t (hsub ht)) hinit
  let F : P × ℝ → E →L[ℝ] E :=
    fun w ↦ Jc w.1 (projIcc l u (h₀.1.trans h₀.2) w.2)
  have hproj : Continuous (projIcc l u (h₀.1.trans h₀.2)) := continuous_projIcc
  have hF : Continuous F := continuous_eval.comp
    ((hc.comp continuous_fst).prodMk (hproj.comp continuous_snd))
  apply (hF.continuousAt.congr_of_eventuallyEq ?_).continuousWithinAt
  filter_upwards [continuous_snd.continuousAt.eventually (isOpen_Ioo.mem_nhds ht)] with w hw
  dsimp only [F, Jc]
  exact congrArg (fun t : Icc l u ↦ J (w.1, t))
    (projIcc_of_mem _ (Ioo_subset_Icc_self hw)).symm

/-- `app:ch_regular_base:lem:buffered-interpolation`: a family of linear
solutions with a common initial value is jointly continuous on its parameter
domain and the whole open time interval. -/
theorem continuousOn_linearEvolution
    {s : Set P} {A J : P × ℝ → E →L[ℝ] E} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) (hA : ContinuousOn A (s ×ˢ Ioo a b))
    (hJ : ∀ p ∈ s, ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ ↦ J (p, τ)) ((A (p, t)).comp (J (p, t))) t)
    (hinit : ∀ p ∈ s, ∀ q ∈ s, J (p, t₀) = J (q, t₀)) :
    ContinuousOn J (s ×ˢ Ioo a b) := by
  have hc : ContinuousOn (fun z : s × ℝ ↦ J (z.1.1, z.2)) (univ ×ˢ Ioo a b) :=
    continuousOn_linearEvolution_univ ht₀
      (hA.comp (continuous_subtype_val.prodMap continuous_id).continuousOn
        (fun z hz ↦ ⟨z.1.2, hz.2⟩))
      (fun p t ht ↦ hJ p.1 p.2 t ht) (fun p q ↦ hinit p.1 p.2 q.1 q.2)
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact hc.comp_continuous
    (((continuous_fst.comp continuous_subtype_val).subtype_mk (fun z ↦ z.2.1)).prodMk
      (continuous_snd.comp continuous_subtype_val)) (fun z ↦ ⟨mem_univ _, z.2.2⟩)

/-- `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`: continuous operator coefficients admit a
jointly continuous evolution with identity initial value on the entire open
time interval. This holds even for an arbitrary topological parameter space
and an arbitrary parameter subset. -/
theorem exists_continuous_linearEvolution [CompleteSpace E]
    {s : Set P} {A : P × ℝ → E →L[ℝ] E} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) (hA : ContinuousOn A (s ×ˢ Ioo a b)) :
    ∃ J : P × ℝ → E →L[ℝ] E, ContinuousOn J (s ×ˢ Ioo a b) ∧
      (∀ p ∈ s, J (p, t₀) = ContinuousLinearMap.id ℝ E) ∧
      ∀ p ∈ s, ∀ t ∈ Ioo a b,
        HasDerivAt (fun τ ↦ J (p, τ)) ((A (p, t)).comp (J (p, t))) t := by
  classical
  have hex (p : s) := exists_linearEvolution_Ioo ht₀ (ContinuousLinearMap.id ℝ E)
    (hA.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht ↦ ⟨p.2, ht⟩))
  choose j hj₀ hj using hex
  let J : P × ℝ → E →L[ℝ] E := fun z ↦
    if hp : z.1 ∈ s then j ⟨z.1, hp⟩ z.2 else ContinuousLinearMap.id ℝ E
  have hval (p : P) (hp : p ∈ s) (t : ℝ) : J (p, t) = j ⟨p, hp⟩ t := by
    dsimp only [J]
    rw [dite_eq_left hp]
  have hinit (p : P) (hp : p ∈ s) : J (p, t₀) = ContinuousLinearMap.id ℝ E := by
    rw [hval p hp]
    exact hj₀ ⟨p, hp⟩
  have hd (p : P) (hp : p ∈ s) (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun τ ↦ J (p, τ)) ((A (p, t)).comp (J (p, t))) t := by
    simp_rw [hval p hp]
    exact hj ⟨p, hp⟩ t ht
  exact ⟨J, continuousOn_linearEvolution ht₀ hA hd
    (fun p hp q hq ↦ (hinit p hp).trans (hinit q hq).symm), hinit, hd⟩

end JanetCartan.ODE
