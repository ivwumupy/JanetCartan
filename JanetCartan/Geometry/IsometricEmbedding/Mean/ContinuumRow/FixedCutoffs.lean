module

public import JanetCartan.Analysis.ContDiff.NestedCutoffs
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Measure
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Cutoffs
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Cutoff

/-!
# Fixed physical cutoffs for the continuum row

For `app:ch_background:defn:bg-row`, the three cutoffs have plateaus on the
balls of radii `r`, `2r`, and `3r`, and compact supports inside the balls of
radii `2r`, `3r`, and `4r`. They are respectively the exterior complement,
measurement, and source cutoffs. The coefficient construction can use the
larger radii `4r < 5r < 6r`. All choices precede the current immersion.

The radius can be chosen below any already constructed finite chart buffer.
The carrier charts and their angular masks are separate constructions.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumRow.FixedCutoffs

open ImageGeometry AmplitudeBound PeriodicLocalL2

variable {n : ℕ} {r : ℝ}

/-- A positive row radius below the reference chart and any prescribed common
carrier buffer (`app:ch_background:defn:bg-row`). -/
theorem exists_radius (G : FlatReference n) {b : ℝ} (hb : 0 < b) :
    ∃ r > 0, 6 * r < G.domain.chartRadius ∧ 6 * r < 1 / 2 ∧ 6 * r < b := by
  have hG : 0 < G.domain.chartRadius :=
    G.domain.coreRadius_pos.trans G.domain.coreRadius_lt_chartRadius
  let a := min G.domain.chartRadius (min (1 / 2 : ℝ) b)
  have ha : 0 < a := lt_min hG (lt_min (by norm_num) hb)
  refine ⟨a / 12, by positivity, ?_, ?_, ?_⟩
  all_goals
    have h₁ : a ≤ G.domain.chartRadius := min_le_left _ _
    have h₂ : a ≤ (1 / 2 : ℝ) := (min_le_right _ _).trans (min_le_left _ _)
    have h₃ : a ≤ b := (min_le_right _ _).trans (min_le_right _ _)
    linarith

/-- The actual exterior, measurement, and source physical cutoffs in that
order (`app:ch_background:defn:bg-row`). -/
def physical (hr : 0 < r) (i : Fin 3) : ContDiffBump (0 : Euclidean n) :=
  bufferedBallBump 0 (((i : ℕ) + 1 : ℝ) * r) (((i : ℕ) + 2 : ℝ) * r)
    (mul_pos (by positivity) hr) (by nlinarith)

/-- Compact support strictly inside the next physical ball
(`app:ch_background:defn:bg-row`). -/
theorem physical_tsupport (hr : 0 < r) (i : Fin 3) :
    tsupport (physical (n := n) hr i) ⊆ ball 0 (((i : ℕ) + 2 : ℝ) * r) :=
  bufferedBallBump_tsupport_subset _ _ _ _ _

/-- Each closed inner ball has an open plateau
(`app:ch_background:defn:bg-row`). -/
theorem physical_plateau (hr : 0 < r) (i : Fin 3) :
    closedBall (0 : Euclidean n) (((i : ℕ) + 1 : ℝ) * r) ⊆
      interior {x | physical hr i x = 1} :=
  bufferedBallBump_plateau _ _ _ _ _

/-- All three supports fit the common coefficient agreement region
(`app:ch_background:defn:bg-row`). -/
theorem physical_tsupport_four (hr : 0 < r) (i : Fin 3) :
    tsupport (physical (n := n) hr i) ⊆ closedBall 0 (4 * r) := by
  apply (physical_tsupport hr i).trans
  apply ball_subset_closedBall.trans (closedBall_subset_closedBall _)
  have hi : (i : ℝ) ≤ 2 := by exact_mod_cast (show i.val ≤ 2 by omega)
  nlinarith

/-- The fixed physical source cutoff is one wherever the measurement cutoff
is nonzero. This supplies the output-test cutoff of the carrier normal
producer with the SAME cutoffs as the image channel
(`app:ch_background:defn:bg-row`). -/
theorem source_one_on_measurement (hr : 0 < r) {x : Euclidean n}
    (hx : physical hr 1 x ≠ 0) : physical hr 2 x = 1 := by
  have hs := physical_tsupport hr 1 (subset_tsupport _ hx)
  have hs' : x ∈ closedBall (0 : Euclidean n) (((2 : Fin 3) + 1 : ℝ) * r) := by
    convert ball_subset_closedBall hs using 1
    norm_num
  have hp : x ∈ {x : Euclidean n | physical hr 2 x = 1} :=
    interior_subset (physical_plateau hr 2 hs')
  exact hp

/-- The fixed physical cutoffs vanish off the common output chart. In
particular the source cutoff is a compact smooth output-test cutoff in the
global carrier-normal construction (`app:ch_background:defn:bg-row`). -/
theorem physical_eq_zero_outside_four (hr : 0 < r) (i : Fin 3)
    {x : Euclidean n} (hx : x ∉ closedBall 0 (4 * r)) : physical hr i x = 0 := by
  by_contra h
  exact hx (physical_tsupport_four hr i (subset_tsupport _ h))

/-- Periodization of the same physical cutoffs, on the unit auxiliary torus
(`app:ch_background:defn:bg-row`). -/
def periodic (hr : 0 < r) (hcell : 4 * r < 1 / 2) (i : Fin 3) : C(Torus n, ℝ) :=
  periodizedImageCutoff hcell (physical hr i) (physical hr i).contDiff
    (physical_tsupport_four hr i)

/-- Literal centered-representative formula (`app:ch_background:defn:bg-row`). -/
@[simp] theorem periodic_apply (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (i : Fin 3) (z : Torus n) :
    periodic hr hcell i z = physical hr i (centeredTorusRepresentative z) := rfl

/-- The fixed torus cutoffs are smooth (`app:ch_background:defn:bg-row`). -/
theorem periodic_smooth (hr : 0 < r) (hcell : 4 * r < 1 / 2) (i : Fin 3) :
    IsSmoothPeriodic (periodic (n := n) hr hcell i) :=
  isSmoothPeriodic_periodizedImageCutoff _ _ _ _

/-- The cutoffs retain their real range under periodization
(`app:ch_background:defn:bg-row`). -/
theorem periodic_mem_Icc (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (i : Fin 3) (z : Torus n) : periodic hr hcell i z ∈ Icc (0 : ℝ) 1 :=
  ⟨(physical hr i).nonneg, (physical hr i).le_one⟩

/-- All three fixed cutoff operators have norm at most one
(`app:ch_background:prop:bg-frame`). -/
theorem periodic_norm_le_one (hr : 0 < r) (hcell : 4 * r < 1 / 2) (i : Fin 3) :
    ‖periodic (n := n) hr hcell i‖ ≤ 1 :=
  norm_periodizedImageCutoff_le_one _ _ _ _
    (fun _ ↦ ⟨(physical hr i).nonneg, (physical hr i).le_one⟩)

/-- The common physical chart is strictly inside the unit cell
(`app:ch_background:defn:bg-row`). -/
theorem closedBall_four_subset_cell (hcell : 4 * r < 1 / 2) :
    closedBall (0 : Euclidean n) (4 * r) ⊆ halfOpenCell n := by
  intro x hx i
  have hxnorm := mem_closedBall_zero_iff.mp hx
  have hi := (PiLp.norm_apply_le x i).trans hxnorm
  rw [Real.norm_eq_abs] at hi
  have hi' := abs_le.mp hi
  constructor <;> linarith

/-- The periodic and physical cutoffs agree, with every jet, on the common
physical chart (`app:ch_background:defn:bg-row`). -/
theorem periodic_eventuallyEq (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (i : Fin 3) {x : Euclidean n} (hx : x ∈ closedBall 0 (4 * r)) :
    periodicLift (periodic hr hcell i) =ᶠ[nhds x] physical hr i :=
  periodizedImageCutoff_eventuallyEq _ _ _ _
    (halfOpenCell_subset_fundamentalCell (closedBall_four_subset_cell hcell hx))

/-- The actual exterior channel is a contraction on the full real torus L²
space (`app:ch_background:prop:bg-frame`). -/
theorem exterior_norm_le_one (hr : 0 < r) (hcell : 4 * r < 1 / 2) :
    ‖exteriorChannel (periodic (n := n) hr hcell 0)‖ ≤ 1 := by
  apply (exteriorChannel_norm_le _).trans
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro z
  change ‖1 - periodic hr hcell 0 z‖ ≤ 1
  have hz := periodic_mem_Icc hr hcell 0 z
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hz.1, hz.2]

/-- The exterior input has zero output on the actual core of radius `r`
(`app:ch_background:prop:bg-frame`). -/
theorem exterior_zero_on_core (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (f : OutputL2 n) :
    ∀ᵐ z ∂volume, centeredTorusRepresentative z ∈ closedBall 0 r →
      exteriorChannel (periodic hr hcell 0) f z = 0 := by
  apply exteriorChannel_zero_on_core (periodic hr hcell 0)
    {z | centeredTorusRepresentative z ∈ closedBall 0 r}
  intro z hz
  change physical hr 0 (centeredTorusRepresentative z) = 1
  change centeredTorusRepresentative z ∈ closedBall 0 r at hz
  have hz' : centeredTorusRepresentative z ∈
      closedBall (0 : Euclidean n) (((0 : Fin 3) + 1 : ℝ) * r) := by
    simpa only [Fin.val_zero, Nat.cast_zero, zero_add, one_mul] using hz
  have hp : centeredTorusRepresentative z ∈ {x : Euclidean n | physical hr 0 x = 1} :=
    interior_subset (physical_plateau hr 0 hz')
  exact hp

end JanetCartan.ContinuumRow.FixedCutoffs
