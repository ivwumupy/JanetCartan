module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMargins
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceProfiles

/-!
# The whole original sampling cell lies on the retained response parameter plateau

The working radius is centered at the incidence **root**, not at the selected
parent cell center. Its closed doubled joint ball lies in the parent's open
σ-cover ball. Projecting therefore gives the original doubled response window
on the entire region tested by the measured sampler, and the actual θ is one
as a germ at each such point. The inclusion holds before source, history, rate
or shift; there is no claim that θ is one throughout the outer source window
(`app:ch_response:eq:response-graded-source`, `app:ch_waves:eq:sampling-operator-bounds`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 1200000

namespace JanetCartan.PhysicalSampling.OriginalResponseWindow
open Set Metric Filter PhysicalSeed PhysicalNormalInverse PhysicalPrimary
open scoped Topology

variable {d : ℕ} (hn : 5 ≤ d + 1) (pOrder : ℕ)
  (εframe : ℝ) (hεframe : 0 < εframe)
  (qext : BallExtension.Parameters (Euclidean (d + 1)))
  (hqcenter : qext.center = 0) (hqradius : qext.radius = OriginalBoundary.b hn)
  (k : (a : Fin (OriginalBoundary.D hn).chartCount) ×
    Fin ((OriginalBoundary.D hn).patchCount a) → Euclidean (d + 1))
  (hk : ∀ a, k a ≠ 0) (hkD : ∀ a, k a ∈ (OriginalBoundary.D hn).domain a.1)
  (p : BallExtension.Parameters (Euclidean (d + 1))) (orders : Finset ℕ)
  (margin extendedMargin : ℕ → ℝ)
  (hmargin : ∀ a ∈ orders, 0 < margin a)
  (hextendedMargin : ∀ a ∈ orders, 0 < extendedMargin a)
  (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hincidenceCap : 0 < incidenceCap)
  (userExtra : StrongExtraCaps hn)

local notation "capped" => strongCappedExtra hn (samplingCappedExtra hn pOrder userExtra)
set_option quotPrecheck false in
local notation "selected(" f ")" =>
  f hn εframe hεframe qext hqcenter hqradius k hk hkD p orders margin extendedMargin
    hmargin hextendedMargin cap hcap incidenceCap hincidenceCap capped
set_option quotPrecheck false in
local notation "actual(" f ")" =>
  f hn pOrder εframe hεframe qext hqcenter hqradius k hk hkD p orders margin extendedMargin
    hmargin hextendedMargin cap hcap incidenceCap hincidenceCap userExtra

set_option quotPrecheck false
local notation "E" => Euclidean (d+1)
local notation "P" => Euclidean 3 × Euclidean ((d+1)-1)
local notation "Row" => actual(OriginalWeights.Index)
local notation "patch(" i ")" => (⟨i.1.1.1.1,i.2⟩ : PhysicalInitialization.OriginalPatchIndex hn)
local notation "cell(" i ")" => selected(SelectedBoundary.cell) i.1.1 i.2
local notation "T(" i ")" => OriginalBoundary.T hn (patch(i))
local notation "root(" i ")" => (OriginalBoundary.D hn).roots i.1.1.1.1 i.2 i.1.1.1.2
local notation "a(" i ")" => ((0 : E),(root(i),(T(i)).reference.spatialPatch (root(i))))
local notation "c(" i ")" => ((cell(i)).1.1,(T(i)).reference.spatialPatch (cell(i)).1.1)
local notation "rho(" i ")" => (originalSamplingRadius hn i.1.1 i.2 (cell(i)) : ℝ)
local notation "rad(" i ")" => OriginalBoundary.σcover hn (patch(i)) (cell(i))
local notation "V(" i ")" => OriginalSourceMasks.parameterWindow hn (patch(i)) (cell(i))
local notation "theta(" i ")" => (OriginalSourceProfiles.parameterCutoff hn (patch(i)) (cell(i)) : P → ℝ)

/-- The *whole closed doubled* sampling ball projects into the parent closed
parameter cell, not just the small set of nonzero sample nodes. -/
theorem doubled_in_parent_cell (i : Row) :
    closedBall (a(i)) (2 * rho(i)) ⊆ (univ : Set E) ×ˢ closedBall (c(i)) (rad(i)) := by
  intro w hw
  have hp := (originalSamplingRadius_spec hn i.1.1 i.2 (cell(i))
    (actual(OriginalAdmission.root_mem) i.1.1 i.2)).1 hw
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hp
  exact ⟨mem_univ _, hp.2.le⟩

/-- Restrict the genuine joint uncut response on univ × V to the exact open
working ball required by the measured sampling kernel. -/
theorem working_open_in_source_window (i : Row) :
    ball (a(i)) (2 * rho(i)) ⊆ (univ : Set E) ×ˢ V(i) := by
  intro w hw
  have h := actual(doubled_in_parent_cell) i (ball_subset_closedBall hw)
  exact ⟨h.1,(OriginalSourceMasks.parameterWindow_spec hn (patch(i)) (cell(i))).2.2.2.2 h.2⟩

/-- At every point of the actual closed doubled working ball, θ pulled back to
all physical/parameter coordinates is identically one as a germ. This retains
all parameter and mixed derivatives; it does not remove θ outside the plateau. -/
theorem parameter_plateau_germ (i : Row) (w : E × P)
    (hw : w ∈ closedBall (a(i)) (2 * rho(i))) :
    (fun q : E × P ↦ theta(i) q.2) =ᶠ[𝓝 w] (1 : E × P → ℝ) := by
  have h := (OriginalSourceProfiles.parameterCutoff_spec hn (patch(i)) (cell(i))).2.2.2 w.2
    (actual(doubled_in_parent_cell) i hw).2
  exact h.comp_tendsto (continuous_snd.tendsto w)

/-- On the sampler's actual closed working compact, multiplication by the
original parameter cutoff does not change *any* mixed jet. The argument uses
local equality, so no separate regularity of a proposed tensor field is needed. -/
theorem parameter_cutoff_preserves_jets {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Row) (g : E × P → F) (j : ℕ) (w : E × P) (hw : w ∈ closedBall (a(i)) (rho(i))) :
    iteratedFDeriv ℝ j (fun v : E × P ↦ theta(i) v.2 • g v) w = iteratedFDeriv ℝ j g w := by
  have hρ : 0 < rho(i) := (originalSamplingRadius hn i.1.1 i.2 (cell(i))).2
  have hd : w ∈ closedBall (a(i)) (2 * rho(i)) :=
    closedBall_subset_closedBall (show rho(i) ≤ 2 * rho(i) by linarith only [hρ]) hw
  have h : (fun v : E × P ↦ theta(i) v.2 • g v) =ᶠ[𝓝 w] g := by
    filter_upwards [actual(parameter_plateau_germ) i w hd] with v hv
    change theta(i) v.2 = 1 at hv
    rw [hv,one_smul]
  exact (h.iteratedFDeriv ℝ j).eq_of_nhds

end JanetCartan.PhysicalSampling.OriginalResponseWindow
end
