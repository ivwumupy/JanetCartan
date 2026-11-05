module

public import JanetCartan.Analysis.Extension.Ball.Regularity.Series.Boundary
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Smooth series on the closed exterior of a ball

The uniform derivative convergence argument following
`app:ch_regular_base:eq:extension-collar-l2`, including the boundary sphere.
Summable majorants at every order give a Taylor series for the sum on the
closed exterior, without any differentiability assumption on that sum.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace JanetCartan.BallExtension

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The sum in the uniform derivative argument after
`app:ch_regular_base:eq:extension-collar-l2`. -/
def smoothSeriesSum (h : ℕ → E → F) (x : E) : F := ∑' k, h k x

namespace Parameters

variable (p : Parameters E)

/-- The candidate jets of the exterior sum, including its sphere values, in the
argument after `app:ch_regular_base:eq:extension-collar-l2`. -/
def exteriorSeriesJet (h : ℕ → E → F) (x : E) : FormalMultilinearSeries ℝ E F :=
  fun m ↦ ∑' k, iteratedFDerivWithin ℝ m (h k) {y | p.radius ≤ ‖y - p.center‖} x

variable {h : ℕ → E → F} {u : ℕ → ℕ → ℝ}

/-- Absolute summability of each exterior jet in the argument after
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem summable_iteratedFDerivWithin_closedExterior
    (hu : ∀ m, Summable (u m))
    (hb : ∀ m k x, p.radius ≤ ‖x - p.center‖ →
      ‖iteratedFDerivWithin ℝ m (h k) {y | p.radius ≤ ‖y - p.center‖} x‖ ≤ u m k)
    (m : ℕ) {x : E} (hx : p.radius ≤ ‖x - p.center‖) :
    Summable (fun k ↦ iteratedFDerivWithin ℝ m (h k)
      {y | p.radius ≤ ‖y - p.center‖} x) :=
  .of_norm_bounded (hu m) (fun k ↦ hb m k x hx)

/-- Uniform convergence of the derivative series on the entire closed exterior,
as asserted after `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem tendstoUniformlyOn_exteriorSeriesJet
    (hu : ∀ m, Summable (u m))
    (hb : ∀ m k x, p.radius ≤ ‖x - p.center‖ →
      ‖iteratedFDerivWithin ℝ m (h k) {y | p.radius ≤ ‖y - p.center‖} x‖ ≤ u m k)
    (m : ℕ) :
    TendstoUniformlyOn
      (fun N x ↦ ∑ k ∈ Finset.range N,
        iteratedFDerivWithin ℝ m (h k) {y | p.radius ≤ ‖y - p.center‖} x)
      (fun x ↦ p.exteriorSeriesJet h x m) atTop {y | p.radius ≤ ‖y - p.center‖} :=
  tendstoUniformlyOn_tsum_nat (hu m) (hb m)

/-- Continuity of each summed exterior jet, including at the sphere, in the
argument after `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem continuousOn_exteriorSeriesJet
    (hh : ∀ k, ContDiffOn ℝ ∞ (h k) {y | p.radius ≤ ‖y - p.center‖})
    (hu : ∀ m, Summable (u m))
    (hb : ∀ m k x, p.radius ≤ ‖x - p.center‖ →
      ‖iteratedFDerivWithin ℝ m (h k) {y | p.radius ≤ ‖y - p.center‖} x‖ ≤ u m k)
    (m : ℕ) :
    ContinuousOn (fun x ↦ p.exteriorSeriesJet h x m) {y | p.radius ≤ ‖y - p.center‖} := by
  exact continuousOn_tsum
    (fun k ↦ ((hh k).ftaylorSeriesWithin p.uniqueDiffOn_closedExterior).cont m (by simp))
    (hu m) (hb m)

/-- Termwise smoothness on the closed exterior, including the sphere, from the
summable bounds used after `app:ch_regular_base:eq:extension-collar-l2`.
The sum and its boundary jets are conclusions of the theorem. -/
theorem hasFTaylorSeriesUpToOn_smoothSeriesSum_closedExterior
    (hh : ∀ k, ContDiffOn ℝ ∞ (h k) {y | p.radius ≤ ‖y - p.center‖})
    (hu : ∀ m, Summable (u m))
    (hb : ∀ m k x, p.radius ≤ ‖x - p.center‖ →
      ‖iteratedFDerivWithin ℝ m (h k) {y | p.radius ≤ ‖y - p.center‖} x‖ ≤ u m k) :
    HasFTaylorSeriesUpToOn ∞ (smoothSeriesSum h) (p.exteriorSeriesJet h)
      {y | p.radius ≤ ‖y - p.center‖} := by
  classical
  let X := {y : E | p.radius ≤ ‖y - p.center‖}
  let U := {y : E | p.radius < ‖y - p.center‖}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
  have hUX : U ⊆ X := fun y hy ↦ (show p.radius < ‖y - p.center‖ from hy).le
  have ht (k : ℕ) := (hh k).ftaylorSeriesWithin p.uniqueDiffOn_closedExterior
  have hs (m : ℕ) {x : E} (hx : x ∈ X) :=
    p.summable_iteratedFDerivWithin_closedExterior hu hb m hx
  refine ⟨?_, ?_, fun m _ ↦ p.continuousOn_exteriorSeriesJet hh hu hb m⟩
  · intro x hx
    change (continuousMultilinearCurryFin0 ℝ E F) (∑' k,
      iteratedFDerivWithin ℝ 0 (h k) X x) = ∑' k, h k x
    exact (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.map_tsum |>.trans
      (tsum_congr (fun k ↦ (ht k).zero_eq x hx))
  · intro m hm x hx
    let C := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F)
    have hc : ContinuousOn (fun y ↦ (p.exteriorSeriesJet h y (m + 1)).curryLeft) X :=
      C.continuous.comp_continuousOn (p.continuousOn_exteriorSeriesJet hh hu hb (m + 1))
    apply p.hasFDerivWithinAt_closedExterior
      (p.continuousOn_exteriorSeriesJet hh hu hb m) hc ?_ hx
    intro y hy
    have hd (k : ℕ) (z : E) (hz : z ∈ U) :
        HasFDerivAt (fun w ↦ iteratedFDerivWithin ℝ m (h k) X w)
          (iteratedFDerivWithin ℝ (m + 1) (h k) X z).curryLeft z :=
      ((ht k).fderivWithin m hm z (hUX hz)).hasFDerivAt
        (mem_of_superset (hU.mem_nhds hz) hUX)
    have hbC (k : ℕ) (z : E) (hz : z ∈ U) :
        ‖(iteratedFDerivWithin ℝ (m + 1) (h k) X z).curryLeft‖ ≤ u (m + 1) k := by
      rw [ContinuousMultilinearMap.curryLeft_norm]
      exact hb (m + 1) k z (hUX hz)
    have hdSum := hasFDerivAt_of_tendstoUniformlyOn hU
      (tendstoUniformlyOn_tsum (hu (m + 1)) hbC)
      (fun t z hz ↦ HasFDerivAt.fun_sum (fun k (_ : k ∈ t) ↦ hd k z hz))
      (fun z hz ↦ (hs m (hUX hz)).hasSum) hy
    change HasFDerivAt (fun z ↦ ∑' k, iteratedFDerivWithin ℝ m (h k) X z)
      (C (∑' k, iteratedFDerivWithin ℝ (m + 1) (h k) X y)) y
    have heq : C (∑' k, iteratedFDerivWithin ℝ (m + 1) (h k) X y) =
        ∑' k, (iteratedFDerivWithin ℝ (m + 1) (h k) X y).curryLeft :=
      C.toContinuousLinearEquiv.map_tsum
    rw [heq]
    exact hdSum

/-- Smoothness of the summed exterior series up to the boundary, as required
following `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem contDiffOn_smoothSeriesSum_closedExterior
    (hh : ∀ k, ContDiffOn ℝ ∞ (h k) {y | p.radius ≤ ‖y - p.center‖})
    (hu : ∀ m, Summable (u m))
    (hb : ∀ m k x, p.radius ≤ ‖x - p.center‖ →
      ‖iteratedFDerivWithin ℝ m (h k) {y | p.radius ≤ ‖y - p.center‖} x‖ ≤ u m k) :
    ContDiffOn ℝ ∞ (smoothSeriesSum h) {y | p.radius ≤ ‖y - p.center‖} :=
  (p.hasFTaylorSeriesUpToOn_smoothSeriesSum_closedExterior hh hu hb).contDiffOn

/-- The actual derivatives of the exterior sum equal the summed jets, also on
the sphere; see the argument after `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem iteratedFDerivWithin_smoothSeriesSum_closedExterior
    (hh : ∀ k, ContDiffOn ℝ ∞ (h k) {y | p.radius ≤ ‖y - p.center‖})
    (hu : ∀ m, Summable (u m))
    (hb : ∀ m k x, p.radius ≤ ‖x - p.center‖ →
      ‖iteratedFDerivWithin ℝ m (h k) {y | p.radius ≤ ‖y - p.center‖} x‖ ≤ u m k)
    (m : ℕ) {x : E} (hx : p.radius ≤ ‖x - p.center‖) :
    iteratedFDerivWithin ℝ m (smoothSeriesSum h) {y | p.radius ≤ ‖y - p.center‖} x =
      p.exteriorSeriesJet h x m :=
  ((p.hasFTaylorSeriesUpToOn_smoothSeriesSum_closedExterior hh hu hb).eq_iteratedFDerivWithin_of_uniqueDiffOn
    (by simp) p.uniqueDiffOn_closedExterior hx).symm

/-- Derivatives of the partial sums converge uniformly to the derivatives of
the sum on the closed exterior, including the sphere, in the argument following
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem tendstoUniformlyOn_iteratedFDerivWithin_partialSum_closedExterior
    (hh : ∀ k, ContDiffOn ℝ ∞ (h k) {y | p.radius ≤ ‖y - p.center‖})
    (hu : ∀ m, Summable (u m))
    (hb : ∀ m k x, p.radius ≤ ‖x - p.center‖ →
      ‖iteratedFDerivWithin ℝ m (h k) {y | p.radius ≤ ‖y - p.center‖} x‖ ≤ u m k)
    (m : ℕ) :
    TendstoUniformlyOn
      (fun N ↦ iteratedFDerivWithin ℝ m (fun x ↦ ∑ k ∈ Finset.range N, h k x)
        {y | p.radius ≤ ‖y - p.center‖})
      (iteratedFDerivWithin ℝ m (smoothSeriesSum h) {y | p.radius ≤ ‖y - p.center‖})
      atTop {y | p.radius ≤ ‖y - p.center‖} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (p.tendstoUniformlyOn_exteriorSeriesJet hu hb m) ε hε] with N hN
  intro x hx
  rw [iteratedFDerivWithin_fun_sum_apply p.uniqueDiffOn_closedExterior hx
    (fun k _ ↦ (hh k x hx).of_le (by simp)),
    p.iteratedFDerivWithin_smoothSeriesSum_closedExterior hh hu hb m hx]
  exact hN x hx

end Parameters

end JanetCartan.BallExtension
