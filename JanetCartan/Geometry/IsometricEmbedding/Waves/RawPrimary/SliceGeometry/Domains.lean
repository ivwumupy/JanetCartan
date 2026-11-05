module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.RefinementSpaces
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualBuffers

/-!
# Original domains for the canonical raw slice phase

The normalized input core contains the entire radius-two wide band. Physical
and epsilon radii can be made smaller independently of that input core.
`sliceShiftDomain` and `sliceClosedCore` are the original `Q` and `H` required
by `SliceBounds.exists_rawPhysicalSliceSobolev_wkbGrades`; they are retained
when the inverse geometry and its finite phase budgets are assembled.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.SliceGeometry
open ActualCarriers FrozenMenu CurrentFullPhase SliceBounds RawInputPartition
open FullPhaseCharts.ActualPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

local notation "E" => Euclidean (n - 1)

/-- Physical domain of the original, unrescaled phase
(`app:ch_waves:eq:individual-raw-slice`). -/
def slicePhysicalDomain (n : ℕ) (a : ℝ) : Set (Euclidean n) := ball 0 (4 * a)

/-- Original physical domain in the consumer's adapted coordinates
(`app:ch_waves:setup:oscillatory`). -/
def sliceAdaptedDomain (a : ℝ) : Set (ℝ × E) :=
  adaptedPhysicalCoordinates T.data.adapted ⁻¹' slicePhysicalDomain n a

/-- Spatial box used by the transverse normal geometry
(`app:ch_osc:setup:osc-normal`). -/
def sliceSpatialDomain (n : ℕ) (a : ℝ) : Set (Euclidean (n - 1)) := ball 0 a

/-- Compact spatial support core, strictly inside the spatial box
(`app:ch_osc:setup:osc-normal`). -/
def sliceSpatialCore (n : ℕ) (a : ℝ) : Set (Euclidean (n - 1)) := closedBall 0 (a / 2)

/-- The convex input domain retains room outside the complete normalized
wide-band support (`app:ch_waves:eq:individual-raw-slice`). -/
def sliceInputDomain (n : ℕ) : Set (Euclidean (n - 1)) := ball 0 3

/-- The entire radius-two input ball is retained, including the high-pass
transition (`app:ch_waves:eq:individual-raw-slice`). -/
def sliceInputCore (n : ℕ) : Set (Euclidean (n - 1)) := closedBall 0 2

/-- Open normalized-input extension for every original shift and derivative
(`app:ch_waves:setup:oscillatory`). -/
def sliceInputExtension (n : ℕ) : Set (Euclidean (n - 1)) := ball 0 4

/-- Epsilon varies on both sides of zero and past the retained endpoint `e`
(`app:ch_seed:eq:seed-quotient-integral`). -/
def sliceParameterDomain (e : ℝ) : Set ℝ := Ioo (-2 * e) (2 * e)

/-- Joint open spatial/input extension of the normal data
(`app:ch_osc:setup:osc-normal`). -/
def sliceExtensionDomain (n : ℕ) (a : ℝ) : Set (Euclidean (n - 1) × Euclidean (n - 1)) :=
  ball 0 (2 * a) ×ˢ sliceInputExtension n

/-- Original joint domain `Q` required by the WKB endpoint. It contains the
whole original physical domain for every admissible input and epsilon
(`app:ch_waves:eq:individual-raw-slice`). -/
def sliceShiftDomain (a e : ℝ) : Set (ℝ × (ℝ × E) × E) :=
  sliceParameterDomain e ×ˢ sliceAdaptedDomain T a ×ˢ sliceInputExtension n

/-- Compact derivative core `H` required by the WKB endpoint. It includes
every retained slice time and every closed spatial/input core point
(`app:ch_waves:eq:individual-raw-slice`). -/
def sliceClosedCore (n : ℕ) (a e : ℝ) :
    Set (ℝ × (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)) :=
  Icc 0 e ×ˢ (closedBall 0 a ×ˢ closedBall 0 a) ×ˢ closedBall 0 3

/-- The normalized original band, with no part of its support removed,
lies in the selected compact input core (`app:ch_waves:setup:oscillatory`). -/
theorem wideBand_zero_subset_sliceInputCore : wideBand n 0 ⊆ sliceInputCore n := by
  intro η hη
  have h : η ∈ closedBall 0 (4 * dyadicScale 0) := hη.1
  norm_num [dyadicScale] at h
  simpa only [sliceInputCore, mem_closedBall, dist_zero_right] using h

/-- The original band also lies strictly inside the smooth input extension
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem wideBand_zero_subset_sliceInputExtension : wideBand n 0 ⊆ sliceInputExtension n :=
  wideBand_zero_subset_sliceInputCore.trans (closedBall_subset_ball (by norm_num))

/-- The physical reconstruction bound used to retain all slice-core points
(`app:ch_waves:setup:oscillatory`). -/
theorem norm_slicePhysicalCoordinates_le (t : ℝ) (y : E) :
    ‖adaptedPhysicalCoordinates T.data.adapted (t, y)‖ ≤ |t| + ‖y‖ := by
  simpa only [adaptedPhysicalCoordinates_apply, norm_smul, Real.norm_eq_abs,
    T.data.adapted.normal_unit, mul_one, LinearIsometry.norm_map] using
      norm_add_le (t • T.data.adapted.normal) (T.data.adapted.embedding y)

/-- Openness of the exact original adapted physical domain
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem isOpen_sliceAdaptedDomain (a : ℝ) : IsOpen (sliceAdaptedDomain T a) :=
  isOpen_ball.preimage (NullTransport.ActualFlow.adaptedCoordinates T.data.adapted).symm.continuous

/-- Openness of the entire original joint shift domain
(`app:ch_seed:eq:seed-quotient-integral`). -/
theorem isOpen_sliceShiftDomain (a e : ℝ) : IsOpen (sliceShiftDomain T a e) :=
  isOpen_Ioo.prod ((isOpen_sliceAdaptedDomain T a).prod isOpen_ball)

/-- The closed epsilon interval has a two-sided open extension
(`app:ch_osc:setup:osc-normal`). -/
theorem sliceParameterDomain_contains {e : ℝ} (he : 0 < e) :
    Icc 0 e ⊆ sliceParameterDomain e := by
  intro ε hε
  exact ⟨by linarith [hε.1], by linarith [hε.2]⟩

/-- Both spatial closures lie inside the joint smooth extension
(`app:ch_osc:setup:osc-normal`). -/
theorem sliceExtensionDomain_contains {a : ℝ} (ha : 0 < a) :
    closure (sliceSpatialDomain n a) ×ˢ closure (sliceInputDomain n) ⊆
      sliceExtensionDomain n a := by
  intro q hq
  exact ⟨closedBall_subset_ball (by linarith) (closure_ball_subset_closedBall hq.1),
    closedBall_subset_ball (by norm_num) (closure_ball_subset_closedBall hq.2)⟩

/-- Exact chart-to-original-domain containment required by the WKB endpoint
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem sliceExtensionDomain_mapsTo_shiftDomain {a e t : ℝ} (ha : 0 < a)
    (ht : t ∈ Ioo (-a) a) :
    MapsTo (fun q : ℝ × (E × E) ↦ (q.1, (t, q.2.1), q.2.2))
      (sliceParameterDomain e ×ˢ sliceExtensionDomain n a) (sliceShiftDomain T a e) := by
  intro q hq
  refine ⟨hq.1, ?_, hq.2.2⟩
  change ‖adaptedPhysicalCoordinates T.data.adapted (t, q.2.1) - 0‖ < 4 * a
  rw [sub_zero]
  have hy : ‖q.2.1‖ < 2 * a := by simpa using hq.2.1
  have ht' : |t| < a := abs_lt.mpr ht
  exact (norm_slicePhysicalCoordinates_le T t q.2.1).trans_lt (by linarith)

/-- The original derivative core is compact
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem isCompact_sliceClosedCore (a e : ℝ) : IsCompact (sliceClosedCore n a e) :=
  isCompact_Icc.prod (((isCompact_closedBall _ _).prod
    (isCompact_closedBall _ _)).prod (isCompact_closedBall _ _))

/-- The compact derivative core lies in the original open domain, including
epsilon endpoints and spatial/input boundaries
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem sliceClosedCore_subset_shiftDomain {a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    sliceClosedCore n a e ⊆ sliceShiftDomain T a e := by
  intro q hq
  refine ⟨sliceParameterDomain_contains he hq.1, ?_,
    closedBall_subset_ball (by norm_num) hq.2.2⟩
  change ‖adaptedPhysicalCoordinates T.data.adapted q.2.1 - 0‖ < 4 * a
  rw [sub_zero]
  have ht : |q.2.1.1| ≤ a := by simpa using hq.2.1.1
  have hy : ‖q.2.1.2‖ ≤ a := by simpa using hq.2.1.2
  exact (norm_slicePhysicalCoordinates_le T q.2.1.1 q.2.1.2).trans_lt (by linarith)

/-- All closed-core slice points required by the WKB endpoint belong to
the SAME retained compact `H` (`app:ch_waves:eq:individual-raw-slice`). -/
theorem sliceClosedCore_contains {a e t ε : ℝ} (ht : t ∈ Ioo (-a) a)
    (hε : ε ∈ Icc 0 e) {q : E × E}
    (hq : q ∈ closure (sliceSpatialDomain n a) ×ˢ closure (sliceInputDomain n)) :
    (ε, (t, q.1), q.2) ∈ sliceClosedCore n a e :=
  ⟨hε, ⟨by simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
              using (abs_lt.mpr ht).le,
    closure_ball_subset_closedBall hq.1⟩, closure_ball_subset_closedBall hq.2⟩

/-- The retained carrier is inside the original source covector buffer,
including carrier points on the compact patch boundary
(`app:ch_waves:thm:leading`). -/
theorem spatialPatch_mem_initial_covector_ball {z : Euclidean 3}
    (hz : z ∈ parameterCube (2 * P.radius)) :
    T.reference.spatialPatch z ∈
      ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)) := by
  simpa only [PatchQuantitativeFamily.reference, CarrierPhaseReference.spatialPatch,
    FrozenPhaseReference.AdaptedSection.baseData, mem_ball, Prod.dist_eq,
    dist_self, max_eq_right dist_nonneg, covectorCenter] using T.patch_buffer z hz

/-- Choose physical, covector and epsilon radii from the fixed patch alone,
with arbitrary physical and covector caps. Every smaller positive physical
or epsilon radius remains admissible. These are actual domain choices, before
the current immersion or any frequency (`app:ch_waves:setup:oscillatory`). -/
theorem exists_slice_domain_radii {z : Euclidean 3}
    (hz : z ∈ parameterCube (2 * P.radius)) {amax bmax : ℝ}
    (ha : 0 < amax) (hb : 0 < bmax) :
    ∃ a₀ > (0 : ℝ), 4 * a₀ ≤ amax ∧ 4 * a₀ < T.family.radius ∧
      ∃ b > (0 : ℝ), b ≤ bmax ∧
        ball (T.reference.spatialPatch z) b ⊆
          ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)) ∧
        ∃ e₀ > (0 : ℝ), 16 * e₀ < b := by
  let a₀ := min (amax / 4) (T.family.radius / 8)
  have ha₀ : 0 < a₀ := lt_min (by positivity) (by have := T.family.radius_pos; positivity)
  have hz' := mem_ball.mp (spatialPatch_mem_initial_covector_ball T hz)
  let R := min T.family.radius (3 * T.family.sourceRadius)
  let d := dist (T.reference.spatialPatch z) (covectorCenter T)
  let b := min bmax ((R - d) / 2)
  have hb' : 0 < b := lt_min hb (by dsimp [R, d]; linarith)
  refine ⟨a₀, ha₀, ?_, ?_, b, hb', min_le_left _ _, ?_, b / 32, by positivity, ?_⟩
  · have := min_le_left (amax / 4) (T.family.radius / 8)
    dsimp only [a₀]; linarith
  · have := min_le_right (amax / 4) (T.family.radius / 8)
    dsimp only [a₀]; linarith [T.family.radius_pos]
  · intro η hη
    have hh := dist_triangle η (T.reference.spatialPatch z) (covectorCenter T)
    have hη' := mem_ball.mp hη
    have hbr : b ≤ (R - d) / 2 := min_le_right _ _
    change dist η (covectorCenter T) < R
    change d < R at hz'
    change dist η (T.reference.spatialPatch z) < b at hη'
    change dist η (covectorCenter T) ≤ dist η (T.reference.spatialPatch z) + d at hh
    linarith
  · linarith

/-- The whole original joint domain admits the required open shifted
segments, with the complete normalized input extension retained
(`app:ch_seed:eq:seed-quotient-integral`). -/
theorem rawSliceShift_mapsTo_sliceShiftDomain (z : Euclidean 3) {a e b : ℝ}
    (he : 0 < e) (heb : 16 * e < b) :
    ∀ s ∈ Ioo (-1 : ℝ) 2, MapsTo (rawSliceShift (T.reference.spatialPatch z) s)
      (sliceShiftDomain T a e) (sliceAdaptedDomain T a ×ˢ ball (T.reference.spatialPatch z) b) := by
  intro s hs q hq
  refine ⟨hq.2.1, ?_⟩
  change dist (T.reference.spatialPatch z + (s * q.1) • q.2.2)
    (T.reference.spatialPatch z) < b
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_mul]
  have hs' : |s| ≤ 2 := abs_le.mpr ⟨by linarith [hs.1], hs.2.le⟩
  have he' : |q.1| ≤ 2 * e :=
    (abs_lt.mpr ⟨by linarith [hq.1.1], hq.1.2⟩).le
  have hη : ‖q.2.2‖ ≤ 4 := by exact (mem_ball_zero_iff.mp hq.2.2).le
  calc
    |s| * |q.1| * ‖q.2.2‖ ≤ 2 * (2 * e) * 4 :=
      mul_le_mul (mul_le_mul hs' he' (abs_nonneg _) (by norm_num)) hη
        (norm_nonneg _) (by positivity)
    _ < b := by linarith

/-- Smoothness on the original joint shift domain, for the SAME phase and
the explicit radii constructed above (`app:ch_waves:setup:oscillatory`). -/
theorem canonicalSlicePhase_smooth_on_shiftDomain (Q : _) (z : Euclidean 3)
    {a e b : ℝ} (ha : 4 * a < T.family.radius) (he : 0 < e) (heb : 16 * e < b)
    (hb : ball (T.reference.spatialPatch z) b ⊆
      ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius))) :
    ContDiffOn ℝ ∞
      (rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z))
      (sliceShiftDomain T a e) := by
  have hS : ContDiffOn ℝ ∞ (Function.uncurry (canonicalBasePhase T Q))
      (sliceAdaptedDomain T a ×ˢ ball (T.reference.spatialPatch z) b) := by
    apply (canonicalBasePhase_smooth T Q).mono
    intro q hq
    refine ⟨ball_subset_ball (by linarith [T.family.radius_pos]) hq.1, ?_⟩
    exact ball_subset_ball ((min_le_left _ _).trans (by linarith [T.family.radius_pos])) (hb hq.2)
  apply contDiffOn_rawSlicePhaseExtension (isOpen_sliceAdaptedDomain T a) isOpen_ball
    (isOpen_sliceShiftDomain T a e) isOpen_Ioo _ hS
    (rawSliceShift_mapsTo_sliceShiftDomain T z he heb)
  intro s hs
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- Joint smoothness on the normal-data extension, across both epsilon
endpoints, for every retained slice time (`app:ch_osc:setup:osc-normal`). -/
theorem canonicalSlicePhase_smooth (Q : _) (z : Euclidean 3)
    {a e b t : ℝ} (ha : 0 < a) (ha' : 4 * a < T.family.radius)
    (he : 0 < e) (heb : 16 * e < b)
    (hb : ball (T.reference.spatialPatch z) b ⊆
      ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)))
    (ht : t ∈ Ioo (-a) a) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (E × E) ↦ canonicalSlicePhase T Q z t q.1 q.2.1 q.2.2)
      (sliceParameterDomain e ×ˢ sliceExtensionDomain n a) :=
  (canonicalSlicePhase_smooth_on_shiftDomain T Q z ha' he heb hb).comp
    (by fun_prop) (sliceExtensionDomain_mapsTo_shiftDomain T ha ht)

end JanetCartan.RawPrimary.SliceGeometry
