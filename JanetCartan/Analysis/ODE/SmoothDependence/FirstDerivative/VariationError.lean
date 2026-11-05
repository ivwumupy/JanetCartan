module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Grönwall estimates for the first variation error

These estimates support the flow argument in
`app:ch_regular_base:lem:buffered-interpolation`. They apply in both time
directions and compare an actual trajectory difference with a candidate
solution of the linearized equation.
-/

@[expose] public section

open Set

namespace JanetCartan.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:lem:common-hamilton-phase`: the differential Grönwall estimate on an
unordered closed time interval, obtained by reversing time when necessary. -/
theorem norm_le_gronwallBound_of_hasDerivAt_uIcc
    {R R' : ℝ → E} {t₀ t δ L ε : ℝ}
    (hd : ∀ τ ∈ uIcc t₀ t, HasDerivAt R (R' τ) τ)
    (hinit : ‖R t₀‖ ≤ δ)
    (hb : ∀ τ ∈ uIcc t₀ t, ‖R' τ‖ ≤ L * ‖R τ‖ + ε) :
    ‖R t‖ ≤ gronwallBound δ L ε |t - t₀| := by
  rcases le_total t₀ t with ht | ht
  · rw [uIcc_of_le ht] at hd hb
    simpa only [abs_of_nonneg (sub_nonneg.mpr ht)] using
      norm_le_gronwallBound_of_norm_deriv_right_le (HasDerivAt.continuousOn hd)
        (fun τ hτ ↦ (hd τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt) hinit
        (fun τ hτ ↦ hb τ (Ico_subset_Icc_self hτ)) t (right_mem_Icc.mpr ht)
  · rw [uIcc_of_ge ht] at hd hb
    have hmem (τ : ℝ) (hτ : τ ∈ Icc (-t₀) (-t)) : -τ ∈ Icc t t₀ := by
      constructor <;> linarith [hτ.1, hτ.2]
    have hdneg (τ : ℝ) (hτ : τ ∈ Icc (-t₀) (-t)) :
        HasDerivAt (fun σ ↦ R (-σ)) (-R' (-τ)) τ := by
      simpa [Function.comp_def] using (hd (-τ) (hmem τ hτ)).scomp τ (hasDerivAt_id τ).neg
    have h := norm_le_gronwallBound_of_norm_deriv_right_le
      (HasDerivAt.continuousOn hdneg)
      (fun τ hτ ↦ (hdneg τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt)
      (by simpa only [neg_neg] using hinit)
      (fun τ hτ ↦ by simpa only [norm_neg] using hb (-τ) (hmem τ (Ico_subset_Icc_self hτ)))
      (-t) (right_mem_Icc.mpr (neg_le_neg ht))
    simpa only [neg_neg, neg_sub_neg, abs_of_nonpos (sub_nonpos.mpr ht), neg_sub] using h

/-- `app:ch_regular_base:lem:buffered-interpolation`: comparison of a trajectory
difference with a solution of its variational equation. The only forcing in
the error equation is the nonlinear Taylor remainder. -/
theorem flow_variation_error_le {f : E → E} {u v : ℝ → E}
    {A J : ℝ → E →L[ℝ] E} {h : E} {t₀ t L ε : ℝ}
    (hu : ∀ τ ∈ uIcc t₀ t, HasDerivAt u (f (u τ)) τ)
    (hv : ∀ τ ∈ uIcc t₀ t, HasDerivAt v (f (v τ)) τ)
    (hJ : ∀ τ ∈ uIcc t₀ t, HasDerivAt J ((A τ).comp (J τ)) τ)
    (hinit : v t₀ - u t₀ = J t₀ h)
    (hA : ∀ τ ∈ uIcc t₀ t, ‖A τ‖ ≤ L)
    (hrem : ∀ τ ∈ uIcc t₀ t,
      ‖f (v τ) - f (u τ) - A τ (v τ - u τ)‖ ≤ ε) :
    ‖v t - u t - J t h‖ ≤ gronwallBound 0 L ε |t - t₀| := by
  apply norm_le_gronwallBound_of_hasDerivAt_uIcc
    (R := fun τ ↦ v τ - u τ - J τ h)
    (R' := fun τ ↦ f (v τ) - f (u τ) - A τ (J τ h))
  · intro τ hτ
    simpa [Pi.sub_def] using ((hv τ hτ).sub (hu τ hτ)).sub
      ((hJ τ hτ).clm_apply (hasDerivAt_const τ h))
  · simp [hinit]
  · intro τ hτ
    calc
      ‖f (v τ) - f (u τ) - A τ (J τ h)‖ =
          ‖A τ (v τ - u τ - J τ h) +
            (f (v τ) - f (u τ) - A τ (v τ - u τ))‖ := by
              congr 1
              rw [map_sub]
              abel
      _ ≤ ‖A τ (v τ - u τ - J τ h)‖ +
            ‖f (v τ) - f (u τ) - A τ (v τ - u τ)‖ := norm_add_le _ _
      _ ≤ ‖A τ‖ * ‖v τ - u τ - J τ h‖ + ε :=
        add_le_add ((A τ).le_opNorm _) (hrem τ hτ)
      _ ≤ L * ‖v τ - u τ - J τ h‖ + ε := by gcongr; exact hA τ hτ

end JanetCartan.ODE
