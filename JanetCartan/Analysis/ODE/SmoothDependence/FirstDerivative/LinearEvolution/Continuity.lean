module

public import JanetCartan.Analysis.ODE.SmoothDependence.FirstDerivative.LinearEvolution.Existence

/-!
# Continuous dependence of linear evolution

The comparison estimate and compact-uniform continuity below supply parameter
continuity for `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`. Parameters need no differentiability.
-/

@[expose] public section

open Set Metric Filter
open scoped Topology NNReal

namespace JanetCartan.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:lem:common-hamilton-phase`: comparison under perturbation of the
linear coefficient, in either time direction. -/
theorem linearEvolution_dist_le_gronwallBound
    {A B J H : ℝ → E →L[ℝ] E} {t₀ t K ε M : ℝ}
    (hJ : ∀ τ ∈ uIcc t₀ t, HasDerivAt J ((A τ).comp (J τ)) τ)
    (hH : ∀ τ ∈ uIcc t₀ t, HasDerivAt H ((B τ).comp (H τ)) τ)
    (hinit : J t₀ = H t₀)
    (hA : ∀ τ ∈ uIcc t₀ t, ‖A τ‖ ≤ K)
    (hAB : ∀ τ ∈ uIcc t₀ t, ‖A τ - B τ‖ ≤ ε)
    (hHbound : ∀ τ ∈ uIcc t₀ t, ‖H τ‖ ≤ M) (hε : 0 ≤ ε) :
    dist (J t) (H t) ≤ gronwallBound 0 K (ε * M) |t - t₀| := by
  rw [dist_eq_norm]
  apply norm_le_gronwallBound_of_hasDerivAt_uIcc
    (R := fun τ ↦ J τ - H τ)
    (R' := fun τ ↦ (A τ).comp (J τ) - (B τ).comp (H τ))
    (fun τ hτ ↦ by simpa only [Pi.sub_def] using (hJ τ hτ).sub (hH τ hτ))
    (by simp [hinit])
  intro τ hτ
  calc
    ‖(A τ).comp (J τ) - (B τ).comp (H τ)‖ =
        ‖(A τ).comp (J τ - H τ) + (A τ - B τ).comp (H τ)‖ := by
      congr 1
      rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
      abel
    _ ≤ ‖(A τ).comp (J τ - H τ)‖ + ‖(A τ - B τ).comp (H τ)‖ := norm_add_le _ _
    _ ≤ ‖A τ‖ * ‖J τ - H τ‖ + ‖A τ - B τ‖ * ‖H τ‖ :=
      add_le_add ((A τ).opNorm_comp_le _) ((A τ - B τ).opNorm_comp_le _)
    _ ≤ K * ‖J τ - H τ‖ + ε * M := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (hA τ hτ) (norm_nonneg _))
        (mul_le_mul (hAB τ hτ) (hHbound τ hτ) (norm_nonneg _) hε)

/-- `app:ch_regular_base:lem:buffered-interpolation`: continuous coefficients
and a common initial value imply compact-uniform continuous dependence of
linear solutions. The parameter space may be any topological space. -/
theorem continuous_linearEvolution_compact
    {P : Type*} [TopologicalSpace P] {a b t₀ : ℝ}
    {A J : P × ℝ → E →L[ℝ] E} (ht₀ : t₀ ∈ Icc a b)
    (hA : ContinuousOn A (univ ×ˢ Icc a b))
    (hJ : ∀ p t, t ∈ Icc a b →
      HasDerivAt (fun τ ↦ J (p, τ)) ((A (p, t)).comp (J (p, t))) t)
    (hinit : ∀ p q, J (p, t₀) = J (q, t₀)) :
    Continuous (fun p ↦ (⟨fun t : Icc a b ↦ J (p, t),
      continuousOn_iff_continuous_domRestrict.mp
        (HasDerivAt.continuousOn (hJ p))⟩ : C(Icc a b, E →L[ℝ] E))) := by
  let Ac : P → C(Icc a b, E →L[ℝ] E) := fun p ↦
    ⟨fun t ↦ A (p, t), hA.comp_continuous
      (continuous_const.prodMk continuous_subtype_val) (fun t ↦ ⟨mem_univ _, t.2⟩)⟩
  let Jc : P → C(Icc a b, E →L[ℝ] E) := fun p ↦
    ⟨fun t ↦ J (p, t), continuousOn_iff_continuous_domRestrict.mp
      (HasDerivAt.continuousOn (hJ p))⟩
  change Continuous Jc
  have hAc : Continuous Ac := ContinuousMap.continuous_of_continuous_uncurry Ac
    (hA.comp_continuous (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun z ↦ ⟨mem_univ _, z.2.2⟩))
  apply continuous_iff_continuousAt.mpr
  intro p
  let K : ℝ := ‖Ac p‖ + 1
  let D : ℝ := max (b - t₀) (t₀ - a)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hev : ∀ᶠ q in 𝓝 p, ‖Ac q‖ < K := by
    have hn : Continuous (fun q ↦ ‖Ac q‖) := (continuous_norm (E := C(Icc a b, E →L[ℝ] E))).comp hAc
    exact hn.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  have hbound : ∀ᶠ q in 𝓝 p, dist (Jc q) (Jc p) ≤
      gronwallBound 0 K (dist (Ac q) (Ac p) * ‖Jc p‖) D := by
    filter_upwards [hev] with q hq
    have heps : 0 ≤ dist (Ac q) (Ac p) * ‖Jc p‖ := mul_nonneg dist_nonneg (norm_nonneg (Jc p))
    have hg (t : Icc a b) : dist (Jc q t) (Jc p t) ≤
        gronwallBound 0 K (dist (Ac q) (Ac p) * ‖Jc p‖) D := by
      have hsub : uIcc t₀ t.1 ⊆ Icc a b := uIcc_subset_Icc ht₀ t.2
      apply (linearEvolution_dist_le_gronwallBound
        (fun τ hτ ↦ hJ q τ (hsub hτ)) (fun τ hτ ↦ hJ p τ (hsub hτ)) (hinit q p)
        (fun τ hτ ↦ ((Ac q).norm_coe_le_norm ⟨τ, hsub hτ⟩).trans hq.le)
        (fun τ hτ ↦ by
          simpa only [dist_eq_norm, Ac, ContinuousMap.coe_mk] using
            ContinuousMap.dist_apply_le_dist (f := Ac q) (g := Ac p) ⟨τ, hsub hτ⟩)
        (fun τ hτ ↦ (Jc p).norm_coe_le_norm ⟨τ, hsub hτ⟩) dist_nonneg).trans
      exact gronwallBound_mono le_rfl heps hK (abs_sub_le_max_sub t.2.1 t.2.2 t₀)
    exact (ContinuousMap.dist_le ((dist_nonneg (x := Jc q ⟨t₀, ht₀⟩)
      (y := Jc p ⟨t₀, ht₀⟩)).trans (hg ⟨t₀, ht₀⟩))).mpr hg
  apply (tendsto_iff_dist_tendsto_zero (f := Jc) (a := Jc p) (x := 𝓝 p)).mpr
  apply squeeze_zero' (Eventually.of_forall (fun q ↦ dist_nonneg)) hbound
  have hdist : Tendsto (fun q ↦ dist (Ac q) (Ac p)) (𝓝 p) (𝓝 0) := by
    exact (tendsto_iff_dist_tendsto_zero (f := Ac) (a := Ac p)).mp hAc.continuousAt
  have heps := hdist.mul_const ‖Jc p‖
  have hlim := (gronwallBound_continuous_ε 0 K D).continuousAt.tendsto.comp heps
  simpa only [zero_mul, gronwallBound_ε0_δ0, Function.comp_def] using hlim

end JanetCartan.ODE
