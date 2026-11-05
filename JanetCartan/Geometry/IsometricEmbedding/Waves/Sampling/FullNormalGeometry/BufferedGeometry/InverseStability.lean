module

public import JanetCartan.Analysis.Calculus.BufferedInverse
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Buffered inverse stability for an arbitrary normalized gap below one

The contraction argument of `paper.tex`, `app:lem:buffered-inverse-stability`,
works for every fixed reference gap `q < 1`. This variant supplies the common
image buffers on the complete convex radial domain required by
`app:ch_seed:prop:seed-phase-charts` and the full radial sampling construction.

The analytic inputs remain explicit: `jc-sampling-radial-frozen-gap` produces
the reference derivative bound, and `jc-sampling-radial-c1-comparison` produces
the value and derivative perturbation bounds. The consumer
`jc-sampling-full-radial-inverse` must instantiate them on its actual maps.
-/

@[expose] public noncomputable section

open Set Metric
open scoped NNReal

namespace JanetCartan.Sampling.FullNormalGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalized contraction argument in `app:lem:buffered-inverse-stability`
puts a ball of radius `(1 - c) * r` in the image. Used below to obtain the
outer image buffer without restricting the reference gap to one quarter. -/
private theorem mem_image_closedBall_of_gap_lt_one [CompleteSpace E]
    {D : Set E} (hD : Convex ℝ D) (G : E ≃L[ℝ] E) {f : E → E} {c : ℝ≥0}
    (hf : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hgap : ∀ x ∈ D,
      ‖(G.symm : E →L[ℝ] E).comp (fderiv ℝ f x) - ContinuousLinearMap.id ℝ E‖ ≤ c)
    {u : E} {r : ℝ} (hr : 0 ≤ r) (hball : closedBall u r ⊆ D)
    {v : E} (hv : ‖G.symm (v - f u)‖ ≤ (1 - (c : ℝ)) * r) :
    v ∈ f '' closedBall u r := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨u, mem_closedBall_self hr, G.symm.injective (Subsingleton.elim _ _)⟩
  have ha := approximatesLinearOn_normalized_of_derivative_gap hD G hf hgap
  have hs := ha.surjOn_closedBall_of_nonlinearRightInverse
    (ContinuousLinearEquiv.refl ℝ E).toNonlinearRightInverse hr hball
  have hv' : G.symm v ∈ closedBall (G.symm (f u))
      ((((ContinuousLinearEquiv.refl ℝ E).toNonlinearRightInverse.nnnorm : ℝ)⁻¹ - c) * r) := by
    simpa [mem_closedBall, dist_eq_norm, ← map_sub,
      ContinuousLinearEquiv.toNonlinearRightInverse] using hv
  obtain ⟨x, hx, heq⟩ := hs hv'
  exact ⟨x, hx, G.symm.injective heq⟩

/-- `app:lem:buffered-inverse-stability` for any reference gap `q < 1`, supplying
the common image buffers in `app:ch_seed:prop:seed-phase-charts` on the full
convex radial domain. One positive ordinary C¹ tolerance `τ`, one positive
buffer `b`, and one relatively compact open `V` work for every perturbation.
Only value closeness on `K` is needed; derivative closeness holds throughout `D`.
No inverse-domain conclusion is assumed. -/
theorem common_buffered_inverse_domains_of_gap_lt_one [FiniteDimensional ℝ E]
    {K D₁ D : Set E} (hK : IsCompact K) (hD₁ : IsOpen D₁)
    (hK₁ : K ⊆ D₁) (h₁D : D₁ ⊆ D) (hD : Convex ℝ D)
    (G : E ≃L[ℝ] E) {q : ℝ≥0} (hq : q < 1) {f₀ : E → E}
    (hf₀ : ∀ x ∈ D, DifferentiableAt ℝ f₀ x)
    (hgap₀ : ∀ x ∈ D,
      ‖(G.symm : E →L[ℝ] E).comp (fderiv ℝ f₀ x) - ContinuousLinearMap.id ℝ E‖ ≤ q) :
    ∃ τ > 0, ∃ b > 0, ∃ V : Set E, IsOpen V ∧ IsCompact (closure V) ∧
      ∀ f : E → E, (∀ x ∈ D, DifferentiableAt ℝ f x) →
        (∀ x ∈ D, ‖fderiv ℝ f x - fderiv ℝ f₀ x‖ ≤ τ) →
        (∀ x ∈ K, ‖f x - f₀ x‖ ≤ τ) →
        InjOn f D ∧ cthickening b (f '' K) ⊆ V ∧
        cthickening b (closure V) ⊆ f '' D₁ := by
  have hq' : (q : ℝ) < 1 := by exact_mod_cast hq
  let c : ℝ≥0 := (q + 1) / 2
  have hc_eq : (c : ℝ) = ((q : ℝ) + 1) / 2 := by simp [c]
  have hc : (c : ℝ) < 1 := by rw [hc_eq]; linarith
  obtain ⟨r, hr, hrK⟩ := hK.exists_cthickening_subset_open hD₁ hK₁
  let C : ℝ := ‖(G.symm : E →L[ℝ] E)‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let b : ℝ := r * (1 - (c : ℝ)) / (16 * C)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbC : b * C = r * (1 - (c : ℝ)) / 16 := by dsimp [b]; field_simp
  let τ : ℝ := min b ((1 - (q : ℝ)) / (2 * C))
  have hτ : 0 < τ := lt_min hb (by positivity)
  have hτb : τ ≤ b := min_le_left _ _
  have hτC : C * τ ≤ (1 - (q : ℝ)) / 2 := by
    have h := min_le_right b ((1 - (q : ℝ)) / (2 * C))
    change τ ≤ (1 - (q : ℝ)) / (2 * C) at h
    have := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp h
    nlinarith
  let S := f₀ '' K
  have hS : IsCompact S := hK.image_of_continuousOn
    (fun x hx ↦ (hf₀ x (h₁D (hK₁ hx))).continuousAt.continuousWithinAt)
  let V := thickening (4 * b) S
  have hVclosure : closure V ⊆ cthickening (4 * b) S :=
    closure_thickening_subset_cthickening _ _
  refine ⟨τ, hτ, b, hb, V, isOpen_thickening,
    hS.cthickening.of_isClosed_subset isClosed_closure hVclosure, ?_⟩
  intro f hf hderiv hvalue
  have hgap : ∀ x ∈ D,
      ‖(G.symm : E →L[ℝ] E).comp (fderiv ℝ f x) - ContinuousLinearMap.id ℝ E‖ ≤ c := by
    intro x hx
    have hnear : ‖(G.symm : E →L[ℝ] E).comp
        (fderiv ℝ f x - fderiv ℝ f₀ x)‖ ≤ (1 - (q : ℝ)) / 2 := by
      calc
        _ ≤ ‖(G.symm : E →L[ℝ] E)‖ * ‖fderiv ℝ f x - fderiv ℝ f₀ x‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ C * τ := by
          gcongr
          · dsimp [C]; linarith
          · exact hderiv x hx
        _ ≤ (1 - (q : ℝ)) / 2 := hτC
    have heq : (G.symm : E →L[ℝ] E).comp (fderiv ℝ f x) -
        ContinuousLinearMap.id ℝ E =
        (G.symm : E →L[ℝ] E).comp (fderiv ℝ f x - fderiv ℝ f₀ x) +
          ((G.symm : E →L[ℝ] E).comp (fderiv ℝ f₀ x) - ContinuousLinearMap.id ℝ E) := by
      ext y
      simp
    rw [heq]
    exact (norm_add_le _ _).trans (by linarith [hgap₀ x hx])
  have ha := approximatesLinearOn_normalized_of_derivative_gap hD G hf hgap
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have h := ha x hx y hy
    simp only [hxy, sub_self, zero_sub, norm_neg, ContinuousLinearMap.id_apply] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (x - y)]))
  · intro v hv
    have hv' := cthickening_subset_thickening' (by positivity : 0 < 2 * b)
      (by linarith : b < 2 * b) (f '' K) hv
    obtain ⟨_, ⟨u, hu, rfl⟩, hvu⟩ := mem_thickening_iff.mp hv'
    apply mem_thickening_iff.mpr
    refine ⟨f₀ u, mem_image_of_mem _ hu, ?_⟩
    have hfu : dist (f u) (f₀ u) ≤ b := by
      simpa [dist_eq_norm] using (hvalue u hu).trans hτb
    calc dist v (f₀ u) ≤ dist v (f u) + dist (f u) (f₀ u) := dist_triangle _ _ _
      _ < 4 * b := by linarith
  · intro v hv
    have hv₁ := cthickening_subset_of_subset b hVclosure hv
    have hv₂ := cthickening_cthickening_subset hb.le (by positivity : 0 ≤ 4 * b) S hv₁
    have hv₃ := cthickening_subset_thickening' (by positivity : 0 < 6 * b)
      (by linarith : b + 4 * b < 6 * b) S hv₂
    obtain ⟨_, ⟨u, hu, rfl⟩, hvu⟩ := mem_thickening_iff.mp hv₃
    have hball : closedBall u r ⊆ D₁ := (closedBall_subset_cthickening hu r).trans hrK
    have hdist : ‖v - f u‖ < 7 * b := by
      have hfu : dist (f₀ u) (f u) ≤ b := by
        simpa [dist_eq_norm, norm_sub_rev] using (hvalue u hu).trans hτb
      have := dist_triangle v (f₀ u) (f u)
      rw [dist_eq_norm] at this
      linarith
    have hnorm : ‖G.symm (v - f u)‖ ≤ (1 - (c : ℝ)) * r := by
      calc
        ‖G.symm (v - f u)‖ ≤ ‖(G.symm : E →L[ℝ] E)‖ * ‖v - f u‖ :=
          (G.symm : E →L[ℝ] E).le_opNorm _
        _ ≤ C * ‖v - f u‖ := by gcongr; dsimp [C]; linarith
        _ ≤ C * (7 * b) := mul_le_mul_of_nonneg_left hdist.le hC.le
        _ ≤ (1 - (c : ℝ)) * r := by nlinarith [hbC]
    exact image_mono hball
      (mem_image_closedBall_of_gap_lt_one hD G hf hgap hr.le (hball.trans h₁D) hnorm)

end JanetCartan.Sampling.FullNormalGeometry
