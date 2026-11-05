module

public import JanetCartan.Analysis.Extension.Ball.Regularity.Gluing
public import JanetCartan.Analysis.Extension.Ball.Regularity.BoundaryMoments
public import JanetCartan.Analysis.Extension.Ball.Regularity.DerivativeBounds
public import JanetCartan.Analysis.Extension.Ball.Regularity.Series

/-!
# Smooth joining for the fixed Seeley ball extension

For `app:ch_regular_base:eq:extension-radial-formula` and the boundary-jet
argument following `app:ch_regular_base:eq:extension-collar-l2`, the summable
coefficient bounds imply uniform convergence of every exterior derivative,
including on the sphere. The infinite moments identify the exterior jets with
the input's interior jets. Gluing across the two closed sets proves smoothness
of the actual extension, first for real values and then in any finite-dimensional
real normed space.

The only coefficient assumptions are the two explicit conditions in
`app:ch_regular_base:eq:extension-infinite-moments`. The input is smooth on the
closed ball; no ambient extension or boundary matching is assumed.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped Topology ContDiff

namespace JanetCartan.BallExtension.Parameters

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (p : JanetCartan.BallExtension.Parameters E)

/-- The coefficient decay in `app:ch_regular_base:eq:extension-infinite-moments`
discharges all derivative majorants for the uniform convergence argument after
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem exists_summable_summand_derivative_majorant
    (a : ℕ → ℝ)
    (ha : ∀ ell : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ell)))
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) :
    ∃ u : ℕ → ℕ → ℝ, (∀ m, Summable (u m)) ∧
      ∀ m k x, p.radius ≤ ‖x - p.center‖ →
        ‖iteratedFDerivWithin ℝ m (fun y ↦ p.summand a f y k)
          {y | p.radius ≤ ‖y - p.center‖} x‖ ≤ u m k := by
  choose C _ hC using p.exists_summand_derivative_bound hf
  refine ⟨fun m k ↦ C m * (|a k| * (2 : ℝ) ^ (k * m)),
    fun m ↦ (ha m).mul_left (C m), ?_⟩
  intro m k x hx
  simpa only [mul_assoc] using hC m a k x hx

/-- The exterior series has the termwise Taylor field, including on the sphere,
as asserted after `app:ch_regular_base:eq:extension-collar-l2`. Only absolute
coefficient decay is needed at this step. -/
theorem hasFTaylorSeriesUpToOn_tsum_summand_closedExterior
    (a : ℕ → ℝ)
    (ha : ∀ ell : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ell)))
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) :
    HasFTaylorSeriesUpToOn ∞ (fun x ↦ ∑' k, p.summand a f x k)
      (p.exteriorSeriesJet (fun k x ↦ p.summand a f x k))
      {y | p.radius ≤ ‖y - p.center‖} := by
  obtain ⟨u, hu, hb⟩ := p.exists_summable_summand_derivative_majorant a ha hf
  exact p.hasFTaylorSeriesUpToOn_smoothSeriesSum_closedExterior
    (p.contDiffOn_summand_closedExterior a hf) hu hb

/-- Smoothness of the actual exterior series up to the sphere, from the
uniform derivative argument following `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem contDiffOn_tsum_summand_closedExterior
    (a : ℕ → ℝ)
    (ha : ∀ ell : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ell)))
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) :
    ContDiffOn ℝ ∞ (fun x ↦ ∑' k, p.summand a f x k)
      {y | p.radius ≤ ‖y - p.center‖} :=
  (p.hasFTaylorSeriesUpToOn_tsum_summand_closedExterior a ha hf).contDiffOn

/-- Termwise differentiation of every order on the closed exterior, including
the sphere, in the argument after `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem iteratedFDerivWithin_tsum_summand_closedExterior
    (a : ℕ → ℝ)
    (ha : ∀ ell : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ell)))
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius))
    (m : ℕ) {x : E} (hx : p.radius ≤ ‖x - p.center‖) :
    iteratedFDerivWithin ℝ m (fun y ↦ ∑' k, p.summand a f y k)
      {y | p.radius ≤ ‖y - p.center‖} x =
      ∑' k, iteratedFDerivWithin ℝ m (fun y ↦ p.summand a f y k)
        {y | p.radius ≤ ‖y - p.center‖} x :=
  ((p.hasFTaylorSeriesUpToOn_tsum_summand_closedExterior a ha hf).eq_iteratedFDerivWithin_of_uniqueDiffOn
    (by simp) p.uniqueDiffOn_closedExterior hx).symm

/-- Uniform convergence of every derivative of the partial sums on the entire
closed exterior, as asserted following `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem tendstoUniformlyOn_iteratedFDerivWithin_summand_partialSum
    (a : ℕ → ℝ)
    (ha : ∀ ell : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ell)))
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (m : ℕ) :
    TendstoUniformlyOn
      (fun N ↦ iteratedFDerivWithin ℝ m (fun x ↦ ∑ k ∈ Finset.range N, p.summand a f x k)
        {y | p.radius ≤ ‖y - p.center‖})
      (iteratedFDerivWithin ℝ m (fun x ↦ ∑' k, p.summand a f x k)
        {y | p.radius ≤ ‖y - p.center‖})
      atTop {y | p.radius ≤ ‖y - p.center‖} := by
  obtain ⟨u, hu, hb⟩ := p.exists_summable_summand_derivative_majorant a ha hf
  exact p.tendstoUniformlyOn_iteratedFDerivWithin_partialSum_closedExterior
    (p.contDiffOn_summand_closedExterior a hf) hu hb m

omit [FiniteDimensional ℝ E] in
/-- The zeroth moment makes the actual piecewise extension equal to the
exterior series on the closed exterior, including the sphere, in
`app:ch_regular_base:eq:extension-radial-formula`. -/
theorem extend_eq_tsum_on_closedExterior (a : ℕ → ℝ)
    (hm : (∑' k, a k) = 1) (f : E → ℝ) :
    EqOn (p.extend a f) (fun x ↦ ∑' k, p.summand a f x k)
      {y | p.radius ≤ ‖y - p.center‖} := by
  intro x hx
  by_cases hxi : ‖x - p.center‖ ≤ p.radius
  · rw [extend, ite_eq_left hxi]
    exact (p.tsum_summand_eq_of_mem_sphere a hm f
      (mem_sphere_iff_norm.mpr (le_antisymm hxi hx))).symm
  · exact ite_eq_right hxi

/-- The actual formula is smooth on the closed exterior, by coefficient decay
and the zeroth moment in `app:ch_regular_base:eq:extension-infinite-moments`. -/
theorem contDiffOn_extend_closedExterior
    (a : ℕ → ℝ)
    (ha : ∀ ell : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ell)))
    (hm : (∑' k, a k) = 1)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) :
    ContDiffOn ℝ ∞ (p.extend a f) {y | p.radius ≤ ‖y - p.center‖} :=
  (p.contDiffOn_tsum_summand_closedExterior a ha hf).congr
    (fun _ hx ↦ p.extend_eq_tsum_on_closedExterior a hm f hx)

/-- All exterior jets of the actual extension equal the input's interior jets
on the sphere. This discharges the matching step after
`app:ch_regular_base:eq:extension-collar-l2` using the infinite moments. -/
theorem iteratedFDerivWithin_extend_closedExterior_of_mem_sphere
    (a : ℕ → ℝ)
    (ha : ∀ ell : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ell)))
    (hm : ∀ ell : ℕ, (∑' k, a k * (-(2 : ℝ) ^ k) ^ ell) = 1)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius))
    (m : ℕ) {x : E} (hx : x ∈ sphere p.center p.radius) :
    iteratedFDerivWithin ℝ m (p.extend a f) {y | p.radius ≤ ‖y - p.center‖} x =
      iteratedFDerivWithin ℝ m f (closedBall p.center p.radius) x := by
  have hxX : p.radius ≤ ‖x - p.center‖ := (mem_sphere_iff_norm.mp hx).ge
  rw [iteratedFDerivWithin_congr
    (p.extend_eq_tsum_on_closedExterior a (by simpa using hm 0) f) hxX m,
    p.iteratedFDerivWithin_tsum_summand_closedExterior a ha hf m hxX]
  exact p.tsum_iteratedFDerivWithin_summand_of_mem_sphere a ha hm hf m hx

/-- The fixed Seeley formula in `app:ch_regular_base:eq:extension-radial-formula`
extends a real-valued function smooth on the closed ball to a globally smooth
function. The two explicit coefficient conditions from
`app:ch_regular_base:eq:extension-infinite-moments` suffice: uniform derivative
convergence and matching across the sphere are proved, not assumed. -/
theorem contDiff_extend
    (a : ℕ → ℝ)
    (ha : ∀ ell : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ell)))
    (hm : ∀ ell : ℕ, (∑' k, a k * (-(2 : ℝ) ^ k) ^ ell) = 1)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) :
    ContDiff ℝ ∞ (p.extend a f) := by
  have hcover : closedBall p.center p.radius ∪ {y : E | p.radius ≤ ‖y - p.center‖} =
      univ := by
    ext x
    simp only [mem_union, mem_closedBall_iff_norm, mem_ofPred_eq, mem_univ, iff_true]
    exact le_total _ _
  rw [← contDiffOn_univ, ← hcover]
  apply contDiffOn_union_of_matching_jets isClosed_closedBall
    (isClosed_le continuous_const (by fun_prop))
    p.uniqueDiffOn_closedBall p.uniqueDiffOn_closedExterior
    (hf.congr (fun _ hx ↦ p.extend_eq_on_closedBall a f hx))
    (p.contDiffOn_extend_closedExterior a ha (by simpa using hm 0) hf)
  intro m x hx
  rw [iteratedFDerivWithin_congr (p.extend_eq_on_closedBall a f) hx.1 m]
  exact (p.iteratedFDerivWithin_extend_closedExterior_of_mem_sphere a ha hm hf m
    (mem_sphere_iff_norm.mpr (le_antisymm (mem_closedBall_iff_norm.mp hx.1) hx.2))).symm

/-- Finite-dimensional vector-valued smoothness of the same formula in
`app:ch_regular_base:lem:ball-extension`. Applying the real-valued theorem to
linear coordinates preserves the fixed cutoff, coefficients, and operator. -/
theorem contDiff_extend_finiteDimensional
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (a : ℕ → ℝ)
    (ha : ∀ ell : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ell)))
    (hm : ∀ ell : ℕ, (∑' k, a k * (-(2 : ℝ) ^ k) ^ ell) = 1)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) :
    ContDiff ℝ ∞ (p.extend a f) := by
  let e := (Module.finBasis ℝ F).equivFunL
  apply e.comp_contDiff_iff.mp
  apply contDiff_pi.mpr
  intro i
  let L : F →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
  have hL : ContDiffOn ℝ ∞ (L ∘ f) (closedBall p.center p.radius) :=
    L.contDiff.comp_contDiffOn hf
  have h := p.contDiff_extend a ha hm hL
  change ContDiff ℝ ∞ (p.extend a (L.toLinearMap ∘ f)) at h
  rw [p.extend_map a L.toLinearMap f] at h
  exact h

end JanetCartan.BallExtension.Parameters
