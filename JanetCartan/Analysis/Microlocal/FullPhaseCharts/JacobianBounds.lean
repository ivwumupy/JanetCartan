module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Frozen
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Uniform Jacobian bounds for full phase charts

The linear-algebra deduction in `app:lem:buffered-inverse-stability`, used by
`app:ch_seed:prop:seed-phase-charts`. A normalized derivative error at most one
half gives invertibility, an inverse norm bound, and a single positive absolute
Jacobian bound. The latter is uniform over the entire closed operator ball,
not merely a pointwise nonvanishing assertion.

These are conditional deductions. The actual full and transverse phase maps,
their differentiability and their quantitative comparison with the frozen maps
must be supplied by the consumer. No Hamilton phase construction is asserted.
-/

@[expose] public noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace JanetCartan.FullPhaseCharts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The linear lower bound behind `app:lem:buffered-inverse-stability`.
Its consumer is the uniform inverse bound for the full phase derivative. -/
theorem norm_le_twice_normalized_image (G : E ≃L[ℝ] E) {A : E →L[ℝ] E}
    (hgap : ‖(G.symm : E →L[ℝ] E).comp A - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2)
    (x : E) : ‖x‖ ≤ 2 * ‖G.symm (A x)‖ := by
  have he := ((G.symm : E →L[ℝ] E).comp A - ContinuousLinearMap.id ℝ E).le_opNorm x
  have hb := mul_le_mul_of_nonneg_right hgap (norm_nonneg x)
  have ht := norm_sub_le (G.symm (A x)) (G.symm (A x) - x)
  change ‖G.symm (A x) - x‖ ≤ _ at he
  rw [sub_sub_cancel] at ht
  linarith

variable [FiniteDimensional ℝ E]

/-- Invertibility follows from the normalized gap; it is not an extra hypothesis
in `app:ch_seed:prop:seed-phase-charts`. -/
theorem bijective_of_normalized_gap (G : E ≃L[ℝ] E) {A : E →L[ℝ] E}
    (hgap : ‖(G.symm : E →L[ℝ] E).comp A - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) :
    Function.Bijective A := by
  have hi : Function.Injective A := by
    intro x y hxy
    have h := norm_le_twice_normalized_image G hgap (x - y)
    simp only [map_sub, hxy, sub_self, map_zero, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- The inverse differential bound `2 ‖G⁻¹‖` in
`app:ch_seed:prop:seed-phase-charts`, deduced solely from the half gap. -/
theorem norm_inverse_le_of_normalized_gap (G : E ≃L[ℝ] E) {A : E →L[ℝ] E}
    (hgap : ‖(G.symm : E →L[ℝ] E).comp A - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) :
    ‖A.inverse‖ ≤ 2 * ‖(G.symm : E →L[ℝ] E)‖ := by
  let e := (LinearEquiv.ofBijective A.toLinearMap
    (bijective_of_normalized_gap G hgap)).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] E) = A := rfl
  rw [← he, ContinuousLinearMap.inverse_equiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  have h := norm_le_twice_normalized_image G hgap (e.symm y)
  have hay : A (e.symm y) = y := by rw [← he]; exact e.apply_symm_apply y
  rw [hay] at h
  calc
    ‖e.symm y‖ ≤ 2 * ‖G.symm y‖ := h
    _ ≤ 2 * (‖(G.symm : E →L[ℝ] E)‖ * ‖y‖) := by
      gcongr
      exact (G.symm : E →L[ℝ] E).le_opNorm y
    _ = _ := by ring

/-- Pointwise nonvanishing needed to obtain the uniform Jacobian gap in
`app:ch_seed:prop:seed-phase-charts`. -/
theorem det_ne_zero_of_normalized_gap (G : E ≃L[ℝ] E) {A : E →L[ℝ] E}
    (hgap : ‖(G.symm : E →L[ℝ] E).comp A - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) :
    A.det ≠ 0 :=
  (LinearEquiv.ofBijective A.toLinearMap
    (bijective_of_normalized_gap G hgap)).isUnit_det'.ne_zero

/-- A single positive Jacobian gap for every operator in the normalized half
ball (`app:ch_seed:prop:seed-phase-charts`). The constant depends only on the
fixed reference `G` on the fixed finite-dimensional space, independently of the
operator, phase, point, and all parameters. Compactness is used only in the
finite-dimensional space of operators. -/
theorem exists_uniform_abs_det_lower_bound (G : E ≃L[ℝ] E) :
    ∃ c > 0, ∀ A : E →L[ℝ] E,
      ‖(G.symm : E →L[ℝ] E).comp A - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 →
      c ≤ |A.det| := by
  let T : (E →L[ℝ] E) → (E →L[ℝ] E) := fun B ↦ (G : E →L[ℝ] E).comp B
  have hT : Continuous T := continuous_const.clm_comp continuous_id
  have hc := (isCompact_closedBall (ContinuousLinearMap.id ℝ E) (1 / 2 : ℝ)).image hT
  obtain ⟨c, hcpos, hc⟩ := hc.exists_forall_le'
    ContinuousLinearMap.continuous_det.abs.continuousOn (a := 0) (by
      rintro A ⟨B, hB, rfl⟩
      apply abs_pos.mpr
      apply det_ne_zero_of_normalized_gap G
      have heq : (G.symm : E →L[ℝ] E).comp (T B) = B := by ext x; simp [T]
      rw [heq]
      simpa only [mem_closedBall, dist_eq_norm] using hB)
  refine ⟨c, hcpos, fun A hA ↦ hc A ?_⟩
  refine ⟨(G.symm : E →L[ℝ] E).comp A, ?_, ?_⟩
  · simpa only [mem_closedBall, dist_eq_norm] using hA
  · ext x
    simp [T]

/-- Uniform bounds for actual differentials from the two quarter-gap inputs of
`app:lem:buffered-inverse-stability`. The same `c` works for every function and
point, so all physical, spectator, and epsilon parameters can be instantiated
without changing the constant in `app:ch_seed:prop:seed-phase-charts`. -/
theorem exists_uniform_fderiv_bounds (G : E ≃L[ℝ] E) :
    ∃ c > 0, ∀ (f₀ f : E → E) (x : E),
      ‖(G.symm : E →L[ℝ] E).comp (fderiv ℝ f₀ x) -
        ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4 →
      ‖(G.symm : E →L[ℝ] E).comp (fderiv ℝ f x - fderiv ℝ f₀ x)‖ ≤ 1 / 4 →
      Function.Bijective (fderiv ℝ f x) ∧
      ‖(fderiv ℝ f x).inverse‖ ≤ 2 * ‖(G.symm : E →L[ℝ] E)‖ ∧
      c ≤ |(fderiv ℝ f x).det| := by
  obtain ⟨c, hc, hdet⟩ := exists_uniform_abs_det_lower_bound G
  refine ⟨c, hc, fun f₀ f x h₀ hnear ↦ ?_⟩
  have hgap := normalized_derivative_gap_of_perturbation G h₀ hnear
  exact ⟨bijective_of_normalized_gap G hgap,
    norm_inverse_le_of_normalized_gap G hgap, hdet _ hgap⟩

/-- Buffered domains and Jacobian bounds under the literal normalized
quarter-error input from phase comparison. This version of
`app:lem:buffered-inverse-stability` retains its normalized lower Lipschitz
estimate and the very same `V` and `δ` when adding the differential conclusions
required by `app:ch_seed:prop:seed-phase-charts`. -/
theorem common_buffered_domains_with_normalized_jacobian_bounds
    {K D₁ D : Set E} (hK : IsCompact K) (hD₁ : IsOpen D₁)
    (hK₁ : K ⊆ D₁) (h₁D : D₁ ⊆ D) (hD : Convex ℝ D)
    (G : E ≃L[ℝ] E) {f₀ : E → E}
    (hf₀ : ∀ x ∈ D, DifferentiableAt ℝ f₀ x)
    (hgap₀ : ∀ x ∈ D,
      ‖(G.symm : E →L[ℝ] E).comp (fderiv ℝ f₀ x) -
        ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) :
    ∃ c > 0, ∃ δ > 0, ∃ V : Set E, IsOpen V ∧ IsCompact (closure V) ∧
      ∀ f : E → E, (∀ x ∈ D, DifferentiableAt ℝ f x) →
        (∀ x ∈ D, ‖(G.symm : E →L[ℝ] E).comp
          (fderiv ℝ f x - fderiv ℝ f₀ x)‖ ≤ 1 / 4) →
        (∀ x ∈ K, ‖f x - f₀ x‖ ≤ δ) →
        InjOn f D ∧
        (∀ x ∈ D, ∀ y ∈ D, ‖x - y‖ / 2 ≤ ‖G.symm (f x - f y)‖) ∧
        IsCompact (f '' K) ∧ cthickening δ (f '' K) ⊆ V ∧
        cthickening δ (closure V) ⊆ f '' D₁ ∧
        (∀ x ∈ D, Function.Bijective (fderiv ℝ f x) ∧
          ‖(fderiv ℝ f x).inverse‖ ≤ 2 * ‖(G.symm : E →L[ℝ] E)‖ ∧
          c ≤ |(fderiv ℝ f x).det|) := by
  obtain ⟨c, hc, hbounds⟩ := exists_uniform_fderiv_bounds G
  obtain ⟨δ, hδ, V, hV, hVc, hstable⟩ :=
    common_buffered_inverse_domains hK hD₁ hK₁ h₁D hD G hf₀ hgap₀
  refine ⟨c, hc, δ, hδ, V, hV, hVc, ?_⟩
  intro f hf hnear hvalue
  obtain ⟨hinj, hlower, hcompact, hinner, houter⟩ := hstable f hf hnear hvalue
  exact ⟨hinj, hlower, hcompact, hinner, houter,
    fun x hx ↦ hbounds f₀ f x (hgap₀ x hx) (hnear x hx)⟩

/-- The full output of `common_buffered_inverse_domains_of_c1_close`, together
with the uniform differential inverse and Jacobian bounds needed by
`app:ch_seed:prop:seed-phase-charts`. All containments, the compact inner set,
the convex outer domain, and both positive buffers are retained. Only the C¹
tolerance is reduced to enforce the half-gap estimate. No inverse or determinant
estimate is assumed. -/
theorem common_buffered_domains_with_jacobian_bounds
    {K D₁ D : Set E} (hK : IsCompact K) (hD₁ : IsOpen D₁)
    (hK₁ : K ⊆ D₁) (h₁D : D₁ ⊆ D) (hD : Convex ℝ D)
    (G : E ≃L[ℝ] E) {f₀ : E → E}
    (hf₀ : ∀ x ∈ D, DifferentiableAt ℝ f₀ x)
    (hgap₀ : ∀ x ∈ D,
      ‖(G.symm : E →L[ℝ] E).comp (fderiv ℝ f₀ x - (G : E →L[ℝ] E))‖ ≤ 1 / 4) :
    ∃ c > 0, ∃ ε > 0, ∃ δ > 0, ∃ V : Set E,
      IsOpen V ∧ IsCompact (closure V) ∧
      ∀ f : E → E, (∀ x ∈ D, DifferentiableAt ℝ f x) →
        (∀ x ∈ D, ‖fderiv ℝ f x - fderiv ℝ f₀ x‖ ≤ ε) →
        (∀ x ∈ K, ‖f x - f₀ x‖ ≤ ε) →
        InjOn f D ∧
        (∀ x ∈ D, ∀ y ∈ D,
          ‖x - y‖ ≤ (2 * (‖(G.symm : E →L[ℝ] E)‖ + 1)) * ‖f x - f y‖) ∧
        IsCompact (f '' K) ∧ cthickening δ (f '' K) ⊆ V ∧
        cthickening δ (closure V) ⊆ f '' D₁ ∧
        (∀ x ∈ D, Function.Bijective (fderiv ℝ f x) ∧
          ‖(fderiv ℝ f x).inverse‖ ≤ 2 * ‖(G.symm : E →L[ℝ] E)‖ ∧
          c ≤ |(fderiv ℝ f x).det|) := by
  obtain ⟨c, hc, hbounds⟩ := exists_uniform_fderiv_bounds G
  obtain ⟨ε₀, hε₀, δ, hδ, V, hV, hVc, hstable⟩ :=
    common_buffered_inverse_domains_of_c1_close hK hD₁ hK₁ h₁D hD G hf₀ hgap₀
  let C := ‖(G.symm : E →L[ℝ] E)‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let ε := min ε₀ (1 / (4 * C))
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hε₀' : ε ≤ ε₀ := min_le_left _ _
  have hεC : C * ε ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp
      (min_le_right ε₀ (1 / (4 * C)))
    change ε * (4 * C) ≤ 1 at h
    nlinarith
  refine ⟨c, hc, ε, hε, δ, hδ, V, hV, hVc, ?_⟩
  intro f hf hderiv hvalue
  obtain ⟨hinj, hlower, hcompact, hinner, houter⟩ := hstable f hf
    (fun x hx ↦ (hderiv x hx).trans hε₀') (fun x hx ↦ (hvalue x hx).trans hε₀')
  refine ⟨hinj, hlower, hcompact, hinner, houter, fun x hx ↦ ?_⟩
  apply hbounds f₀ f x
  · convert hgap₀ x hx using 2
    ext y
    simp
  · calc
      _ ≤ ‖(G.symm : E →L[ℝ] E)‖ * ‖fderiv ℝ f x - fderiv ℝ f₀ x‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * ε := by
        gcongr
        · dsimp [C]; linarith
        · exact hderiv x hx
      _ ≤ 1 / 4 := hεC

/-- Shrinking around transverse frozen incidence provides a fixed neighborhood
and uniform Jacobian gap for every phase perturbation satisfying the normalized
quarter-error estimate (`app:ch_seed:prop:seed-phase-charts`). This directly
consumes `exists_frozen_derivative_gap` and the explicit triangular equivalence;
the perturbation estimate remains the phase-comparison input. -/
theorem exists_frozen_perturbation_fderiv_bounds
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] {v : ℝ → H} {u : ℝ × H}
    (hv : ContDiffAt ℝ 1 v u.1) (hinc : ⟪deriv v u.1, u.2⟫_ℝ ≠ 0) :
    ∃ ρ > 0, ∃ c > 0, ∀ (f : (ℝ × H) → (ℝ × H)) (w : ℝ × H),
      w ∈ ball u ρ →
      ‖((triangularEquiv _ (v u.1) hinc).symm : (ℝ × H) →L[ℝ] (ℝ × H)).comp
        (fderiv ℝ f w - fderiv ℝ (frozenChart v) w)‖ ≤ 1 / 4 →
      Function.Bijective (fderiv ℝ f w) ∧
      ‖(fderiv ℝ f w).inverse‖ ≤
        2 * ‖((triangularEquiv _ (v u.1) hinc).symm : (ℝ × H) →L[ℝ] (ℝ × H))‖ ∧
      c ≤ |(fderiv ℝ f w).det| := by
  obtain ⟨ρ, hρ, hgap⟩ := exists_frozen_derivative_gap hv hinc
  obtain ⟨c, hc, hbound⟩ := exists_uniform_fderiv_bounds (triangularEquiv _ (v u.1) hinc)
  exact ⟨ρ, hρ, c, hc, fun f w hw hnear ↦ hbound (frozenChart v) f w (hgap w hw) hnear⟩

/-- Transverse maps use the identity reference in
`app:ch_seed:prop:seed-phase-charts`. Their differential inverse has norm at
most two and their absolute Jacobian has one positive lower bound, uniform over
all points and all maps satisfying the half-gap estimate. -/
theorem exists_transverse_fderiv_bounds :
    ∃ c > 0, ∀ (f : E → E) (x : E),
      ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 →
      Function.Bijective (fderiv ℝ f x) ∧
      ‖(fderiv ℝ f x).inverse‖ ≤ 2 ∧ c ≤ |(fderiv ℝ f x).det| := by
  obtain ⟨c, hc, hdet⟩ := exists_uniform_abs_det_lower_bound (ContinuousLinearEquiv.refl ℝ E)
  refine ⟨c, hc, fun f x hgap ↦ ?_⟩
  have hgap' : ‖((ContinuousLinearEquiv.refl ℝ E).symm : E →L[ℝ] E).comp
      (fderiv ℝ f x) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 := by simpa using hgap
  refine ⟨bijective_of_normalized_gap _ hgap', ?_, hdet _ hgap'⟩
  exact (norm_inverse_le_of_normalized_gap _ hgap').trans (by
    simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl]
    have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)
    linarith)

end JanetCartan.FullPhaseCharts
