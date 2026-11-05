module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.InitialBuffer

/-!
# One fixed cutoff for the flow and geometric normal

The flow and normal extensions in `app:ch_background:prop:bg-adjoint` use
this same fixed chart bump. Its plateau contains the complete original
mask support. Its closed support is contained in a larger supported chart,
so `exists_supportedChart_initialBuffer_cap` supplies all flow-working-set
and initial-footpoint containments before the immersion varies.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow PhaseExtension FullPhaseCharts.ActualComparison

variable {n : ℕ}

/-- Center in the literal physical/carrier order of the original canonical
chart (`app:ch_background:eq:bg-T`). -/
def chartCenter (z₀ : Euclidean 3) : Euclidean n × CarrierParameter :=
  (0, z₀ 0, spectatorCenter z₀)

/-- A product ball about the fixed chart center lies in the complete
supported chart, allowing the fixed flow-buffer cap to be applied to cutoff
supports (`app:ch_background:prop:bg-adjoint`). -/
theorem closedBall_chartCenter_subset_supportedChart (z₀ : Euclidean 3)
    {a : ℝ} (ha : 0 ≤ a) :
    closedBall (chartCenter (n := n) z₀) a ⊆ supportedChart z₀ (2 * a) := by
  intro p hp
  have hh : dist p.1 0 ≤ a ∧ dist p.2 (z₀ 0, spectatorCenter z₀) ≤ a := by
    simpa only [chartCenter, mem_closedBall, Prod.dist_eq, max_le_iff] using hp
  have hz : dist p.2.1 (z₀ 0) ≤ a ∧ dist p.2.2 (spectatorCenter z₀) ≤ a := by
    simpa only [Prod.dist_eq, max_le_iff] using hh.2
  exact ⟨hh.1.trans (by linarith), by
    simpa only [CanonicalConic.carrierSupport, mem_prod, mem_closedBall,
      mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hz⟩

/-- A single fixed bump, with plateau radius `8a` and support radius `12a`,
for the flow and geometric normal extensions. The constants precede both
the immersion and the original initial scalar
(`app:ch_background:prop:bg-adjoint`). -/
def chartBump (z₀ : Euclidean 3) {a : ℝ} (ha : 0 < a) :
    ContDiffBump (chartCenter (n := n) z₀) where
  rIn := 8 * a
  rOut := 12 * a
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The chart cutoff equals one on a neighborhood of every point of the
complete original mask support, including its boundary
(`app:ch_background:eq:bg-T`). -/
theorem chartBump_eventuallyEq_one (z₀ : Euclidean 3) {a : ℝ} (ha : 0 < a)
    {p : Euclidean n × CarrierParameter} (hp : p ∈ supportedChart z₀ a) :
    (chartBump z₀ ha : (Euclidean n × CarrierParameter) → ℝ) =ᶠ[𝓝 p] 1 := by
  apply (chartBump z₀ ha).eventuallyEq_one_of_mem_ball
  change dist p (chartCenter z₀) < 8 * a
  rw [chartCenter, Prod.dist_eq, max_lt_iff, Prod.dist_eq, max_lt_iff]
  exact ⟨(mem_closedBall.mp hp.1).trans_lt (by linarith),
    (mem_closedBall.mp hp.2.1).trans_lt (by linarith),
    (mem_closedBall.mp hp.2.2).trans_lt (by linarith)⟩

/-- The closed extension support is controlled by the same family of
supported charts. Taking `24a` below the fixed cap from `InitialBuffer`
places it in the actual flow working cylinder
(`app:ch_background:prop:bg-adjoint`). -/
theorem chartBump_tsupport_subset (z₀ : Euclidean 3) {a : ℝ} (ha : 0 < a) :
    tsupport (chartBump (n := n) z₀ ha) ⊆ supportedChart z₀ (24 * a) := by
  rw [(chartBump z₀ ha).tsupport_eq]
  change closedBall (chartCenter z₀) (12 * a) ⊆ supportedChart z₀ (24 * a)
  simpa only [show 2 * (12 * a) = 24 * a by ring] using
    closedBall_chartCenter_subset_supportedChart (n := n) z₀ (by positivity : 0 ≤ 12 * a)

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
