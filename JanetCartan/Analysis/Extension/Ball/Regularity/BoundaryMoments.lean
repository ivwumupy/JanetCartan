module

public import JanetCartan.Analysis.Extension.Ball.Regularity.BoundaryMoments.Radial

/-!
# All boundary moments of the Seeley ball extension

The infinite moments in `app:ch_regular_base:eq:extension-infinite-moments`
identify the sum of the exterior jets with the interior jets on the sphere.
This formalizes the boundary-jet argument following
`app:ch_regular_base:eq:extension-collar-l2`, directly for one-sided derivatives
of the input, without an ambient extension.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace JanetCartan.BallExtension.Parameters

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (p : JanetCartan.BallExtension.Parameters E)

/-- Uniqueness of the interior jets used after
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem uniqueDiffOn_closedBall : UniqueDiffOn ℝ (closedBall p.center p.radius) := by
  apply uniqueDiffOn_convex (convex_closedBall p.center p.radius)
  exact ⟨p.center, ball_subset_interior_closedBall (mem_ball_self p.radius_pos)⟩

/-- Near the sphere on the exterior side, each fixed sampling map lands in the
input ball, as required in `app:ch_regular_base:eq:extension-radial-formula`. -/
theorem eventually_radialPoint_mem_closedBall_of_mem_sphere {x : E}
    (hx : x ∈ sphere p.center p.radius) (k : ℕ) :
    ∀ᶠ y in 𝓝[{y | p.radius ≤ ‖y - p.center‖}] x,
      p.radialPoint k y ∈ closedBall p.center p.radius := by
  have hs : ContinuousAt (fun y : E ↦ (2 : ℝ) ^ k * (‖y - p.center‖ - p.radius)) x := by
    fun_prop
  have hlt : (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) < p.width := by
    simpa only [mem_sphere_iff_norm.mp hx, sub_self, mul_zero] using p.width_pos
  filter_upwards [self_mem_nhdsWithin,
    (hs.eventually (gt_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds] with y hy hky
  exact p.radialPoint_mem_closedBall_of_scaled_lt hy hky

/-- The cutoff is identically one near each boundary point for each fixed term;
therefore it contributes no boundary jets in the argument after
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem summand_eventuallyEq_smul_comp_radialPoint_of_mem_sphere
    (a : ℕ → ℝ) (f : E → F) {x : E} (hx : x ∈ sphere p.center p.radius) (k : ℕ) :
    (fun y ↦ p.summand a f y k) =ᶠ[𝓝[{y | p.radius ≤ ‖y - p.center‖}] x]
      (fun y ↦ a k • f (p.radialPoint k y)) := by
  have hs : ContinuousAt (fun y : E ↦ (2 : ℝ) ^ k * (‖y - p.center‖ - p.radius)) x := by
    fun_prop
  have hlt : (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) < p.width / 4 := by
    rw [mem_sphere_iff_norm.mp hx, sub_self, mul_zero]
    linarith [p.width_pos]
  filter_upwards [self_mem_nhdsWithin,
    (hs.eventually (gt_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds] with y hy hky
  have hc := p.cutoff_eq_one (mul_nonneg (by positivity) (sub_nonneg.mpr hy)) hky.le
  simp only [summand, hc, mul_one]

/-- The one-sided chain rule for radial sampling at the sphere, used in the
boundary-jet argument after `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem iteratedFDerivWithin_comp_radialPoint_of_mem_sphere {f : E → F}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) {x : E}
    (hx : x ∈ sphere p.center p.radius) (k m : ℕ) :
    iteratedFDerivWithin ℝ m (f ∘ p.radialPoint k) {y | p.radius ≤ ‖y - p.center‖} x =
      (ftaylorSeriesWithin ℝ f (closedBall p.center p.radius) x).taylorComp
        (ftaylorSeries ℝ (p.radialPoint k) x) m := by
  have hxc : x ≠ p.center := by
    intro h
    have hn := mem_sphere_iff_norm.mp hx
    simp only [h, sub_self, norm_zero] at hn
    exact p.radius_pos.ne' hn.symm
  have hxX : x ∈ {y | p.radius ≤ ‖y - p.center‖} :=
    (mem_sphere_iff_norm.mp hx).ge
  have hfx : ContDiffWithinAt ℝ ∞ f (closedBall p.center p.radius) (p.radialPoint k x) := by
    rw [p.radialPoint_eq_self_of_mem_sphere hx]
    exact hf x (sphere_subset_closedBall hx)
  have he : ftaylorSeriesWithin ℝ (p.radialPoint k) {y | p.radius ≤ ‖y - p.center‖} x =
      ftaylorSeries ℝ (p.radialPoint k) x := by
    funext j
    exact iteratedFDerivWithin_eq_iteratedFDeriv p.uniqueDiffOn_closedExterior
      ((p.contDiffAt_radialPoint k hxc).of_le (by simp)) hxX
  rw [iteratedFDerivWithin_comp_of_eventually_mem hfx
    (p.contDiffAt_radialPoint k hxc).contDiffWithinAt p.uniqueDiffOn_closedBall
    p.uniqueDiffOn_closedExterior hxX
    (p.eventually_radialPoint_mem_closedBall_of_mem_sphere hx k) (by simp),
    p.radialPoint_eq_self_of_mem_sphere hx, he]

/-- Each exterior boundary jet is the weighted Faà di Bruno expression in an
affine family of radial jets. This is the step before applying
`app:ch_regular_base:eq:extension-infinite-moments`. -/
theorem iteratedFDerivWithin_summand_eq_taylorComp_of_mem_sphere
    (a : ℕ → ℝ) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) {x : E}
    (hx : x ∈ sphere p.center p.radius) (k m : ℕ) :
    iteratedFDerivWithin ℝ m (fun y ↦ p.summand a f y k)
        {y | p.radius ≤ ‖y - p.center‖} x =
      a k • (ftaylorSeriesWithin ℝ f (closedBall p.center p.radius) x).taylorComp
        (fun j ↦ iteratedFDeriv ℝ j p.radialBase x +
          (-(2 : ℝ) ^ k) • iteratedFDeriv ℝ j p.radialSlope x) m := by
  have hxc : x ≠ p.center := by
    intro h
    have hn := mem_sphere_iff_norm.mp hx
    simp only [h, sub_self, norm_zero] at hn
    exact p.radius_pos.ne' hn.symm
  have hxX : x ∈ {y | p.radius ≤ ‖y - p.center‖} :=
    (mem_sphere_iff_norm.mp hx).ge
  have hfx : ContDiffWithinAt ℝ ∞ f (closedBall p.center p.radius) (p.radialPoint k x) := by
    rw [p.radialPoint_eq_self_of_mem_sphere hx]
    exact hf x (sphere_subset_closedBall hx)
  have hcomp : ContDiffWithinAt ℝ ∞ (f ∘ p.radialPoint k)
      {y | p.radius ≤ ‖y - p.center‖} x :=
    hfx.comp_of_preimage_mem_nhdsWithin x
      (p.contDiffAt_radialPoint k hxc).contDiffWithinAt
      (p.eventually_radialPoint_mem_closedBall_of_mem_sphere hx k)
  have he := p.summand_eventuallyEq_smul_comp_radialPoint_of_mem_sphere a f hx k
  rw [he.iteratedFDerivWithin_eq (he.self_of_nhdsWithin hxX) m]
  change iteratedFDerivWithin ℝ m (a k • (f ∘ p.radialPoint k))
    {y | p.radius ≤ ‖y - p.center‖} x = _
  rw [iteratedFDerivWithin_const_smul_apply (hcomp.of_le (by simp))
    p.uniqueDiffOn_closedExterior hxX,
    p.iteratedFDerivWithin_comp_radialPoint_of_mem_sphere hf hx]
  congr 2
  funext j
  exact p.iteratedFDeriv_radialPoint_eq_base_add_slope hxc k j

/-- The identity is the unit for the one-sided jet composition used after
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem taylorComp_id_eq_iteratedFDerivWithin {f : E → F}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) {x : E}
    (hx : x ∈ closedBall p.center p.radius) (m : ℕ) :
    (ftaylorSeriesWithin ℝ f (closedBall p.center p.radius) x).taylorComp
      (ftaylorSeries ℝ (id : E → E) x) m =
        iteratedFDerivWithin ℝ m f (closedBall p.center p.radius) x := by
  have he : ftaylorSeriesWithin ℝ (id : E → E) (closedBall p.center p.radius) x =
      ftaylorSeries ℝ (id : E → E) x := by
    funext j
    exact iteratedFDerivWithin_eq_iteratedFDeriv p.uniqueDiffOn_closedBall contDiffAt_id hx
  have h := iteratedFDerivWithin_comp (f := (id : E → E)) (g := f) (hf x hx)
    (contDiffWithinAt_id (n := ∞)) p.uniqueDiffOn_closedBall p.uniqueDiffOn_closedBall
    hx (mapsTo_id _) (i := m) (by simp)
  simpa only [Function.comp_id, id_eq, he] using h.symm

/-- All exterior boundary jets sum to the interior jets, by exactly the two
coefficient conditions in `app:ch_regular_base:eq:extension-infinite-moments`.
This is the boundary-jet identification after
`app:ch_regular_base:eq:extension-collar-l2`; `HasSum` gives convergence in the multilinear-map norm. -/
theorem hasSum_iteratedFDerivWithin_summand_of_mem_sphere
    (a : ℕ → ℝ)
    (ha : ∀ ell : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ell)))
    (hm : ∀ ell : ℕ, (∑' k, a k * (-(2 : ℝ) ^ k) ^ ell) = 1)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius))
    (m : ℕ) {x : E} (hx : x ∈ sphere p.center p.radius) :
    HasSum (fun k ↦ iteratedFDerivWithin ℝ m (fun y ↦ p.summand a f y k)
      {y | p.radius ≤ ‖y - p.center‖} x)
      (iteratedFDerivWithin ℝ m f (closedBall p.center p.radius) x) := by
  have hxc : x ≠ p.center := by
    intro h
    have hn := mem_sphere_iff_norm.mp hx
    simp only [h, sub_self, norm_zero] at hn
    exact p.radius_pos.ne' hn.symm
  simp_rw [p.iteratedFDerivWithin_summand_eq_taylorComp_of_mem_sphere a hf hx]
  have h := hasSum_taylorComp_affine_moments a ha hm
    (ftaylorSeriesWithin ℝ f (closedBall p.center p.radius) x)
    (ftaylorSeries ℝ p.radialBase x) (ftaylorSeries ℝ p.radialSlope x) m
  have he : (fun j ↦ ftaylorSeries ℝ p.radialBase x j + ftaylorSeries ℝ p.radialSlope x j) =
      ftaylorSeries ℝ (id : E → E) x := by
    funext j
    exact p.iteratedFDeriv_radialBase_add_radialSlope hxc j
  rw [he, p.taylorComp_id_eq_iteratedFDerivWithin hf (sphere_subset_closedBall hx)] at h
  exact h

/-- Summability of every exterior boundary jet, as asserted following
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem summable_iteratedFDerivWithin_summand_of_mem_sphere
    (a : ℕ → ℝ)
    (ha : ∀ ell : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ell)))
    (hm : ∀ ell : ℕ, (∑' k, a k * (-(2 : ℝ) ^ k) ^ ell) = 1)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius))
    (m : ℕ) {x : E} (hx : x ∈ sphere p.center p.radius) :
    Summable (fun k ↦ iteratedFDerivWithin ℝ m (fun y ↦ p.summand a f y k)
      {y | p.radius ≤ ‖y - p.center‖} x) :=
  (p.hasSum_iteratedFDerivWithin_summand_of_mem_sphere a ha hm hf m hx).summable

/-- The sum of every exterior boundary jet equals the corresponding interior
jet, by `app:ch_regular_base:eq:extension-infinite-moments`. -/
theorem tsum_iteratedFDerivWithin_summand_of_mem_sphere
    (a : ℕ → ℝ)
    (ha : ∀ ell : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ell)))
    (hm : ∀ ell : ℕ, (∑' k, a k * (-(2 : ℝ) ^ k) ^ ell) = 1)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius))
    (m : ℕ) {x : E} (hx : x ∈ sphere p.center p.radius) :
    (∑' k, iteratedFDerivWithin ℝ m (fun y ↦ p.summand a f y k)
      {y | p.radius ≤ ‖y - p.center‖} x) =
      iteratedFDerivWithin ℝ m f (closedBall p.center p.radius) x :=
  (p.hasSum_iteratedFDerivWithin_summand_of_mem_sphere a ha hm hf m hx).tsum_eq

end JanetCartan.BallExtension.Parameters
