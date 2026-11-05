module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Common buffered inverse domains

Quantitative inverse-domain stability from paper.tex,
`app:lem:buffered-inverse-stability`. We normalize the derivative by the fixed
linear equivalence `G`. All norms of linear maps below are operator norms.
The statements apply to arbitrary convex domains and compact inner sets,
and hence to the nested bounded boxes in the manuscript.
-/

@[expose] public noncomputable section

open Set Metric
open scoped NNReal

namespace JanetCartan

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `app:lem:buffered-inverse-stability`: the segment estimate after normalization by `G`. -/
theorem approximatesLinearOn_normalized_of_derivative_gap
    {D : Set E} (hD : Convex ℝ D) (G : E ≃L[ℝ] F) {f : E → F} {c : ℝ≥0}
    (hf : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hgap : ∀ x ∈ D,
      ‖(G.symm : F →L[ℝ] E).comp (fderiv ℝ f x) - ContinuousLinearMap.id ℝ E‖ ≤ c) :
    ApproximatesLinearOn (fun x ↦ G.symm (f x)) (ContinuousLinearMap.id ℝ E) D c := by
  intro x hx y hy
  exact hD.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz ↦ ((G.symm : F →L[ℝ] E).hasFDerivAt.comp z
      (hf z hz).hasFDerivAt).hasFDerivWithinAt) hgap hy hx

/-- `app:lem:buffered-inverse-stability`: the uniform lower Lipschitz estimate. -/
theorem normalized_lower_lipschitz_of_derivative_gap
    {D : Set E} (hD : Convex ℝ D) (G : E ≃L[ℝ] F) {f : E → F}
    (hf : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hgap : ∀ x ∈ D,
      ‖(G.symm : F →L[ℝ] E).comp (fderiv ℝ f x) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2)
    {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    ‖x - y‖ / 2 ≤ ‖G.symm (f x - f y)‖ := by
  have h := approximatesLinearOn_normalized_of_derivative_gap hD G hf
    (c := (1 / 2 : ℝ≥0)) (by simpa using hgap) x hx y hy
  simp only [ContinuousLinearMap.id_apply, ← map_sub, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat] at h
  have hn := norm_sub_le (G.symm (f x - f y)) (G.symm (f x - f y) - (x - y))
  rw [sub_sub_cancel] at hn
  linarith

/-- `app:lem:buffered-inverse-stability`: a derivative gap of one half gives injectivity. -/
theorem injOn_of_normalized_derivative_gap
    {D : Set E} (hD : Convex ℝ D) (G : E ≃L[ℝ] F) {f : E → F}
    (hf : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hgap : ∀ x ∈ D,
      ‖(G.symm : F →L[ℝ] E).comp (fderiv ℝ f x) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) :
    InjOn f D := by
  intro x hx y hy hxy
  have h := normalized_lower_lipschitz_of_derivative_gap hD G hf hgap hx hy
  rw [hxy, sub_self, map_zero, norm_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (by linarith [norm_nonneg (x - y)]))

/-- `app:lem:buffered-inverse-stability`: the image contains an explicit normalized ball.
This is the quantitative inverse function theorem, proved in Mathlib by contraction. -/
theorem mem_image_closedBall_of_normalized_derivative_gap [CompleteSpace E]
    {D : Set E} (hD : Convex ℝ D) (G : E ≃L[ℝ] F) {f : E → F}
    (hf : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hgap : ∀ x ∈ D,
      ‖(G.symm : F →L[ℝ] E).comp (fderiv ℝ f x) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2)
    {u : E} {r : ℝ} (hr : 0 ≤ r) (hball : closedBall u r ⊆ D)
    {v : F} (hv : ‖G.symm (v - f u)‖ ≤ r / 2) : v ∈ f '' closedBall u r := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨u, mem_closedBall_self hr, G.symm.injective (Subsingleton.elim _ _)⟩
  have ha := approximatesLinearOn_normalized_of_derivative_gap hD G hf
    (c := (1 / 2 : ℝ≥0)) (by simpa using hgap)
  have hs := ha.surjOn_closedBall_of_nonlinearRightInverse
    (ContinuousLinearEquiv.refl ℝ E).toNonlinearRightInverse hr hball
  have hv' : G.symm v ∈ closedBall (G.symm (f u))
      ((((ContinuousLinearEquiv.refl ℝ E).toNonlinearRightInverse.nnnorm : ℝ)⁻¹ -
        (1 / 2 : ℝ≥0)) * r) := by
    norm_num [mem_closedBall, dist_eq_norm, ← map_sub,
      ContinuousLinearEquiv.toNonlinearRightInverse]
    linarith
  obtain ⟨x, hx, heq⟩ := hs hv'
  exact ⟨x, hx, G.symm.injective heq⟩

/-- `app:lem:buffered-inverse-stability`: a quarter-size perturbation of the
reference derivative leaves a uniform half-size gap. -/
theorem normalized_derivative_gap_of_perturbation
    (G : E ≃L[ℝ] F) {A B : E →L[ℝ] F}
    (hA : ‖(G.symm : F →L[ℝ] E).comp A - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4)
    (hB : ‖(G.symm : F →L[ℝ] E).comp (B - A)‖ ≤ 1 / 4) :
    ‖(G.symm : F →L[ℝ] E).comp B - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 := by
  have heq : (G.symm : F →L[ℝ] E).comp B - ContinuousLinearMap.id ℝ E =
      (G.symm : F →L[ℝ] E).comp (B - A) +
        ((G.symm : F →L[ℝ] E).comp A - ContinuousLinearMap.id ℝ E) := by
    ext x
    simp
  rw [heq]
  exact (norm_add_le _ _).trans (by linarith)

/-- `app:lem:buffered-inverse-stability`, in quantitative form. Here `K` is the
closure of the inner box and `D₁` is its open buffered chart inside the convex
domain `D`. The same `V` and positive buffer `δ` work for every perturbation
with the displayed C⁰ and C¹ bounds, including every member of a parameter family.

Both compact containments are explicit: the closed `δ`-neighborhood of `f '' K`
lies in `V`, and that of `closure V` lies in `f '' D₁`. The lower Lipschitz
estimate is in the fixed normalized coordinates of the manuscript. -/
theorem common_buffered_inverse_domains [CompleteSpace E] [ProperSpace F]
    {K D₁ D : Set E} (hK : IsCompact K) (hD₁ : IsOpen D₁)
    (hK₁ : K ⊆ D₁) (h₁D : D₁ ⊆ D) (hD : Convex ℝ D)
    (G : E ≃L[ℝ] F) {f₀ : E → F}
    (hf₀ : ∀ x ∈ D, DifferentiableAt ℝ f₀ x)
    (hgap₀ : ∀ x ∈ D,
      ‖(G.symm : F →L[ℝ] E).comp (fderiv ℝ f₀ x) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) :
    ∃ δ > 0, ∃ V : Set F, IsOpen V ∧ IsCompact (closure V) ∧
      ∀ f : E → F, (∀ x ∈ D, DifferentiableAt ℝ f x) →
        (∀ x ∈ D, ‖(G.symm : F →L[ℝ] E).comp
          (fderiv ℝ f x - fderiv ℝ f₀ x)‖ ≤ 1 / 4) →
        (∀ x ∈ K, ‖f x - f₀ x‖ ≤ δ) →
        InjOn f D ∧
        (∀ x ∈ D, ∀ y ∈ D, ‖x - y‖ / 2 ≤ ‖G.symm (f x - f y)‖) ∧
        IsCompact (f '' K) ∧ cthickening δ (f '' K) ⊆ V ∧
        cthickening δ (closure V) ⊆ f '' D₁ := by
  obtain ⟨r, hr, hrK⟩ := hK.exists_cthickening_subset_open hD₁ hK₁
  let C : ℝ := ‖(G.symm : F →L[ℝ] E)‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let δ : ℝ := r / (16 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδC : δ * C = r / 16 := by dsimp [δ]; field_simp
  let S := f₀ '' K
  have hS : IsCompact S := hK.image_of_continuousOn
    (fun x hx ↦ (hf₀ x (h₁D (hK₁ hx))).continuousAt.continuousWithinAt)
  let V := thickening (4 * δ) S
  have hVclosure : closure V ⊆ cthickening (4 * δ) S :=
    closure_thickening_subset_cthickening _ _
  refine ⟨δ, hδ, V, isOpen_thickening,
    hS.cthickening.of_isClosed_subset isClosed_closure hVclosure, ?_⟩
  intro f hf hnear hvalue
  have hgap : ∀ x ∈ D,
      ‖(G.symm : F →L[ℝ] E).comp (fderiv ℝ f x) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 :=
    fun x hx ↦ normalized_derivative_gap_of_perturbation G (hgap₀ x hx) (hnear x hx)
  refine ⟨injOn_of_normalized_derivative_gap hD G hf hgap,
    fun x hx y hy ↦ normalized_lower_lipschitz_of_derivative_gap hD G hf hgap hx hy,
    hK.image_of_continuousOn
      (fun x hx ↦ (hf x (h₁D (hK₁ hx))).continuousAt.continuousWithinAt), ?_, ?_⟩
  · intro v hv
    have hv' := cthickening_subset_thickening' (by positivity : 0 < 2 * δ)
      (by linarith : δ < 2 * δ) (f '' K) hv
    obtain ⟨_, ⟨u, hu, rfl⟩, hvu⟩ := mem_thickening_iff.mp hv'
    apply mem_thickening_iff.mpr
    refine ⟨f₀ u, mem_image_of_mem _ hu, ?_⟩
    have hfu : dist (f u) (f₀ u) ≤ δ := by simpa [dist_eq_norm] using hvalue u hu
    calc dist v (f₀ u) ≤ dist v (f u) + dist (f u) (f₀ u) := dist_triangle _ _ _
      _ < 4 * δ := by linarith
  · intro v hv
    have hv₁ := cthickening_subset_of_subset δ hVclosure hv
    have hv₂ := cthickening_cthickening_subset hδ.le (by positivity : 0 ≤ 4 * δ) S hv₁
    have hv₃ := cthickening_subset_thickening' (by positivity : 0 < 6 * δ)
      (by linarith : δ + 4 * δ < 6 * δ) S hv₂
    obtain ⟨_, ⟨u, hu, rfl⟩, hvu⟩ := mem_thickening_iff.mp hv₃
    have hball : closedBall u r ⊆ D₁ := (closedBall_subset_cthickening hu r).trans hrK
    have hdist : ‖v - f u‖ < 7 * δ := by
      have hfu : dist (f₀ u) (f u) ≤ δ := by
        simpa [dist_eq_norm, norm_sub_rev] using hvalue u hu
      have := dist_triangle v (f₀ u) (f u)
      rw [dist_eq_norm] at this
      linarith
    have hnorm : ‖G.symm (v - f u)‖ ≤ r / 2 := by
      calc
        ‖G.symm (v - f u)‖ ≤ ‖(G.symm : F →L[ℝ] E)‖ * ‖v - f u‖ :=
          (G.symm : F →L[ℝ] E).le_opNorm _
        _ ≤ C * ‖v - f u‖ := by gcongr; dsimp [C]; linarith
        _ ≤ C * (7 * δ) := mul_le_mul_of_nonneg_left hdist.le hC.le
        _ ≤ r / 2 := by nlinarith [hδC]
    exact image_mono hball
      (mem_image_closedBall_of_normalized_derivative_gap hD G hf hgap hr.le
        (hball.trans h₁D) hnorm)

/-- `app:lem:buffered-inverse-stability`: a single positive C¹ tolerance suffices.
The reference gap is written exactly as `G⁻¹ (Df₀ - G)`. Ordinary uniform
value and derivative bounds imply the normalized bounds in
`common_buffered_inverse_domains`; no inverse-domain conclusion is assumed.
For nested boxes take `K = closure D₀`. Smoothness near the outer closed box
implies the differentiability hypotheses used here. -/
theorem common_buffered_inverse_domains_of_c1_close [CompleteSpace E] [ProperSpace F]
    {K D₁ D : Set E} (hK : IsCompact K) (hD₁ : IsOpen D₁)
    (hK₁ : K ⊆ D₁) (h₁D : D₁ ⊆ D) (hD : Convex ℝ D)
    (G : E ≃L[ℝ] F) {f₀ : E → F}
    (hf₀ : ∀ x ∈ D, DifferentiableAt ℝ f₀ x)
    (hgap₀ : ∀ x ∈ D,
      ‖(G.symm : F →L[ℝ] E).comp (fderiv ℝ f₀ x - (G : E →L[ℝ] F))‖ ≤ 1 / 4) :
    ∃ ε > 0, ∃ δ > 0, ∃ V : Set F, IsOpen V ∧ IsCompact (closure V) ∧
      ∀ f : E → F, (∀ x ∈ D, DifferentiableAt ℝ f x) →
        (∀ x ∈ D, ‖fderiv ℝ f x - fderiv ℝ f₀ x‖ ≤ ε) →
        (∀ x ∈ K, ‖f x - f₀ x‖ ≤ ε) →
        InjOn f D ∧
        (∀ x ∈ D, ∀ y ∈ D,
          ‖x - y‖ ≤ (2 * (‖(G.symm : F →L[ℝ] E)‖ + 1)) * ‖f x - f y‖) ∧
        IsCompact (f '' K) ∧ cthickening δ (f '' K) ⊆ V ∧
        cthickening δ (closure V) ⊆ f '' D₁ := by
  have hgap₀' : ∀ x ∈ D,
      ‖(G.symm : F →L[ℝ] E).comp (fderiv ℝ f₀ x) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4 := by
    intro x hx
    convert hgap₀ x hx using 2
    ext y
    simp
  obtain ⟨δ, hδ, V, hV, hVc, hstable⟩ :=
    common_buffered_inverse_domains hK hD₁ hK₁ h₁D hD G hf₀ hgap₀'
  let C : ℝ := ‖(G.symm : F →L[ℝ] E)‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let ε := min δ (1 / (4 * C))
  have hε : 0 < ε := lt_min hδ (by positivity)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεC : ε * C ≤ 1 / 4 := by
    have h := min_le_right δ (1 / (4 * C))
    change ε ≤ 1 / (4 * C) at h
    have := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp h
    nlinarith
  refine ⟨ε, hε, δ, hδ, V, hV, hVc, ?_⟩
  intro f hf hderiv hvalue
  have hnear : ∀ x ∈ D,
      ‖(G.symm : F →L[ℝ] E).comp (fderiv ℝ f x - fderiv ℝ f₀ x)‖ ≤ 1 / 4 := by
    intro x hx
    calc
      _ ≤ ‖(G.symm : F →L[ℝ] E)‖ * ‖fderiv ℝ f x - fderiv ℝ f₀ x‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * ε := by
        gcongr
        · dsimp [C]; linarith
        · exact hderiv x hx
      _ ≤ 1 / 4 := by nlinarith [hεC]
  obtain ⟨hinj, hlower, hcompact, hinner, houter⟩ :=
    hstable f hf hnear (fun x hx ↦ (hvalue x hx).trans hεδ)
  refine ⟨hinj, ?_, hcompact, hinner, houter⟩
  intro x hx y hy
  have hl := hlower x hx y hy
  have hn := (G.symm : F →L[ℝ] E).le_opNorm (f x - f y)
  change ‖G.symm (f x - f y)‖ ≤ ‖(G.symm : F →L[ℝ] E)‖ * ‖f x - f y‖ at hn
  nlinarith [norm_nonneg (f x - f y)]

end JanetCartan
