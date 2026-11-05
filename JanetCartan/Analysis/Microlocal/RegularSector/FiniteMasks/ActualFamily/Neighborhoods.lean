module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.LocalCharts

/-!
# Angular neighborhoods from the actual source-mask plateau

The radial section and all radii are those of the retained local producer.
The open spatial cone is pulled back through the selected `coordinateSplit`;
no common transverse coordinate is presumed.
Consumer: the finite masks in `app:ch_regular_base:thm:sector` and the source
and time plateaux in `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.FiniteMasks.ActualFamily
open Characteristic Characteristic.ResidualCoordinates
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
variable {Ω : Set (Euclidean (d + 1))} {x ξ : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)}

namespace LocalChart

/-- A fixed margin inside the original source, target and amplitude buffers
(`app:ch_regular_base:thm:sector`, finite neighborhood). -/
def neighborhoodRadius (c : LocalChart Ω x RQ A₀ ξ M) : ℝ :=
  min (c.maskRadius / 8) (min (c.bufferRadius / 4) (min (c.targetRadius / 4) (c.rootRadius / 4)))

/-- The common local margin is positive (`thm:sector`). -/
theorem neighborhoodRadius_pos (c : LocalChart Ω x RQ A₀ ξ M) :
    0 < c.neighborhoodRadius :=
  lt_min (div_pos c.maskRadius_pos (by norm_num))
    (lt_min (div_pos c.bufferRadius_pos (by norm_num))
      (lt_min (div_pos c.targetRadius_pos (by norm_num))
        (div_pos c.rootRadius_pos (by norm_num))))

/-- The angular source section lies strictly inside the original plateau
(`energy-complete-residual`). -/
theorem neighborhoodRadius_lt_mask (c : LocalChart Ω x RQ A₀ ξ M) :
    c.neighborhoodRadius < c.maskRadius / 4 :=
  (min_le_left _ _).trans_lt (by have := c.maskRadius_pos; linarith)

/-- The actual normalized angular cone. Its section is a small ball about
this chart's original spatial covector (`thm:sector`). -/
def spatialCone (c : LocalChart Ω x RQ A₀ ξ M) : Set (Euclidean d) :=
  {η | 0 < c.radialSection η ∧
    (c.radialSection η)⁻¹ • η ∈
      ball (coordinateSplit c.index ξ).2 c.neighborhoodRadius}

/-- The cone is open, including the normalization condition (`thm:sector`). -/
theorem isOpen_spatialCone (c : LocalChart Ω x RQ A₀ ξ M) : IsOpen c.spatialCone := by
  have hpos : IsOpen {η | 0 < c.radialSection η} :=
    isOpen_lt continuous_const c.radialSection.continuous
  have hn : ContinuousOn (fun η : Euclidean d ↦ (c.radialSection η)⁻¹ • η)
      {η : Euclidean d | 0 < c.radialSection η} := by
    intro η hη
    have hne : c.radialSection η ≠ 0 := ne_of_gt hη
    exact ((c.radialSection.continuous.continuousAt.inv₀ hne).smul
      (continuousAt_id : ContinuousAt (id : Euclidean d → Euclidean d) η)).continuousWithinAt
  change IsOpen ({η : Euclidean d | 0 < c.radialSection η} ∩
    (fun η : Euclidean d ↦ (c.radialSection η)⁻¹ • η) ⁻¹'
      ball (coordinateSplit c.index ξ).2 c.neighborhoodRadius)
  exact hn.isOpen_inter_preimage hpos isOpen_ball

/-- Zero is excluded by the positive section (`retarded-kernel`). -/
theorem zero_notMem_spatialCone (c : LocalChart Ω x RQ A₀ ξ M) :
    (0 : Euclidean d) ∉ c.spatialCone := by
  intro h
  have := h.1
  simp at this

/-- Positive dilation preserves the SAME normalized section (`thm:sector`). -/
theorem smul_mem_spatialCone (c : LocalChart Ω x RQ A₀ ξ M)
    {η : Euclidean d} (hη : η ∈ c.spatialCone) {t : ℝ} (ht : 0 < t) :
    t • η ∈ c.spatialCone := by
  refine ⟨by simpa using mul_pos ht hη.1, ?_⟩
  have hn : (c.radialSection (t • η))⁻¹ • (t • η) =
      (c.radialSection η)⁻¹ • η := by
    rw [map_smul, smul_eq_mul, mul_inv_rev, smul_smul]
    simp [ht.ne']
  simpa only [hn] using hη.2

/-- The original frozen spatial covector belongs to its constructed cone
(`thm:sector`). -/
theorem center_mem_spatialCone (c : LocalChart Ω x RQ A₀ ξ M) :
    (coordinateSplit c.index ξ).2 ∈ c.spatialCone := by
  constructor
  · rw [c.section_eq_one]; exact zero_lt_one
  · simpa only [c.section_eq_one, inv_one, one_smul] using
      mem_ball_self c.neighborhoodRadius_pos

/-- The angular neighborhood in the ORIGINAL physical coordinates. Every
chart keeps its own selected transverse index (`thm:sector`). -/
def angularNeighborhood (c : LocalChart Ω x RQ A₀ ξ M) : Set E :=
  (fun ζ ↦ (coordinateSplit c.index ζ).2) ⁻¹' c.spatialCone

/-- The actual angular neighborhood is open (`thm:sector`). -/
theorem isOpen_angularNeighborhood (c : LocalChart Ω x RQ A₀ ξ M) :
    IsOpen c.angularNeighborhood :=
  c.isOpen_spatialCone.preimage (coordinateSplit c.index).continuous.snd

/-- Every frozen zero is covered by its OWN constructed chart (`thm:sector`). -/
theorem center_mem_angularNeighborhood (c : LocalChart Ω x RQ A₀ ξ M) :
    ξ ∈ c.angularNeighborhood := c.center_mem_spatialCone

/-- Physical neighborhood in the selected coordinates, before any field or
accuracy is chosen (`thm:sector`). -/
def physicalNeighborhood (c : LocalChart Ω x RQ A₀ ξ M) : Set E :=
  coordinateSplit c.index ⁻¹' ball (coordinateSplit c.index x) c.neighborhoodRadius

/-- Openness permits a common physical ball after finite selection (`thm:sector`). -/
theorem isOpen_physicalNeighborhood (c : LocalChart Ω x RQ A₀ ξ M) :
    IsOpen c.physicalNeighborhood :=
  isOpen_ball.preimage (coordinateSplit c.index).continuous

/-- The physical center belongs to every selected neighborhood (`thm:sector`). -/
theorem center_mem_physicalNeighborhood (c : LocalChart Ω x RQ A₀ ξ M) :
    x ∈ c.physicalNeighborhood := mem_ball_self c.neighborhoodRadius_pos

/-- The SAME source mask is one on the normalized diagonal, as a germ,
throughout the constructed physical and angular neighborhoods. This is the
source plateau used by `energy-complete-residual`. -/
theorem sourceMask_diagonal_plateau (c : LocalChart Ω x RQ A₀ ξ M)
    {y ζ : E} (hy : y ∈ c.physicalNeighborhood) (hζ : ζ ∈ c.angularNeighborhood) :
    ((coordinateSplit c.index y).1, ((coordinateSplit c.index y).2,
      (c.radialSection (coordinateSplit c.index ζ).2)⁻¹ •
        (coordinateSplit c.index ζ).2)) ∈ interior {w | c.sourceMask w = 1} := by
  apply c.sourceMask_plateau
  have hy' : dist (coordinateSplit c.index y) (coordinateSplit c.index x) <
      c.neighborhoodRadius := hy
  have hζ' := hζ.2
  simp only [mem_closedBall, Prod.dist_eq, max_le_iff]
  rw [Prod.dist_eq, max_lt_iff] at hy'
  exact ⟨(hy'.1.trans c.neighborhoodRadius_lt_mask).le,
    (hy'.2.trans c.neighborhoodRadius_lt_mask).le,
    (hζ'.trans c.neighborhoodRadius_lt_mask).le⟩

/-- The SAME time mask equals one as a germ on the selected physical
neighborhood (`energy-complete-residual`). -/
theorem timeMask_plateau_of_mem (c : LocalChart Ω x RQ A₀ ξ M)
    {y : E} (hy : y ∈ c.physicalNeighborhood) :
    c.timeMask =ᶠ[𝓝 (coordinateSplit c.index y).1] (fun _ ↦ 1) := by
  apply mem_of_superset (isOpen_interior.mem_nhds (c.timeMask_plateau ?_)) interior_subset
  have h := (le_max_left _ _).trans_lt (show
    max (dist (coordinateSplit c.index y).1 (coordinateSplit c.index x).1)
      (dist (coordinateSplit c.index y).2 (coordinateSplit c.index x).2) <
        c.neighborhoodRadius from hy)
  exact (h.trans c.neighborhoodRadius_lt_mask).le

/-- The original source support stays above the fixed lower time endpoint;
this is inherited from its actual support radius (`retarded-kernel`). -/
theorem sourceMask_lower_buffer (c : LocalChart Ω x RQ A₀ ξ M) :
    tsupport c.sourceMask ⊆ {w | (coordinateSplit c.index x).1 - c.maskRadius < w.1} := by
  intro w hw
  have hs := c.sourceMask_support hw
  rw [mem_ball, Prod.dist_eq] at hs
  have ht := (le_max_left _ _).trans_lt hs
  have hl := (abs_lt.mp (show |w.1 - (coordinateSplit c.index x).1| <
    c.maskRadius / 2 from ht)).1
  have := c.maskRadius_pos
  change (coordinateSplit c.index x).1 - c.maskRadius < w.1
  linarith

end LocalChart
end JanetCartan.RegularSector.FiniteMasks.ActualFamily
