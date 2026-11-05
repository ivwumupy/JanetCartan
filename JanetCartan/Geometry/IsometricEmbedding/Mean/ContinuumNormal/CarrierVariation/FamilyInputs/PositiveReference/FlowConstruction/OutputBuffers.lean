module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Comparison

/-!
# Concrete compact physical and carrier output buffers

The fixed coordinate maps send positive-radius balls into the common compact
output cylinder. This supplies the range premises of the actual family
comparison before its output order and tolerance are chosen
(`app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow
open ContinuumRow ContinuumRow.CanonicalCarrier

/-- Positive-radius physical and carrier balls, with doubled compact buffers,
map into the fixed common output cylinder. The range follows only from the
fixed linear coordinate changes, and is independent of all flows, immersions,
orders and tolerances (`app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem exists_compact_output_balls {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (z : CarrierParameter) {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) :
    ∃ r > (0 : ℝ),
      IsCompact (closedBall ((0 : Euclidean n), parameter z) (2 * r)) ∧
      IsCompact (closedBall ((0 : Euclidean n), z) (2 * r)) ∧
      MapsTo (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted))
        (closedBall ((0 : Euclidean n), parameter z) (2 * r))
        (outputCylinder ((0 : Euclidean (n - 1)), parameter z) R τ) ∧
      MapsTo (densityCoordinates T) (closedBall ((0 : Euclidean n), z) (2 * r))
        (outputCylinder ((0 : Euclidean (n - 1)), parameter z) R τ) := by
  let p₀ := ((0 : Euclidean (n - 1)), parameter z)
  let C := FlowAmplitude.coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let V := Ioo (-(τ / 2)) (τ / 2) ×ˢ ball p₀ (R / 64)
  have hV : IsOpen V := isOpen_Ioo.prod isOpen_ball
  have hcenter : ((0 : ℝ), p₀) ∈ V :=
    ⟨⟨by linarith, by linarith⟩, mem_ball_self (by positivity)⟩
  have hC : C ((0 : Euclidean n), parameter z) = (0, p₀) := by
    simp [C, p₀, FlowAmplitude.coordinates_apply]
  have hD : densityCoordinates T ((0 : Euclidean n), z) = (0, p₀) := by
    change C ((0 : Euclidean n), parameter z) = (0, p₀)
    exact hC
  have hP : C ⁻¹' V ∈ nhds ((0 : Euclidean n), parameter z) :=
    (hV.preimage C.continuous).mem_nhds (by simpa only [mem_preimage, hC] using hcenter)
  have hX : densityCoordinates T ⁻¹' V ∈ nhds ((0 : Euclidean n), z) :=
    (hV.preimage (densityCoordinates T).continuous).mem_nhds
      (by simpa only [mem_preimage, hD] using hcenter)
  obtain ⟨rP, hrP, hballP⟩ := Metric.mem_nhds_iff.mp hP
  obtain ⟨rX, hrX, hballX⟩ := Metric.mem_nhds_iff.mp hX
  let r := min rP rX / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrP' : 2 * r < rP := by have := min_le_left rP rX; dsimp [r]; linarith
  have hrX' : 2 * r < rX := by have := min_le_right rP rX; dsimp [r]; linarith
  have hVL : V ⊆ outputCylinder p₀ R τ :=
    fun _ hw ↦ ⟨Ioo_subset_Icc_self hw.1, ball_subset_closedBall hw.2⟩
  refine ⟨r, hr, isCompact_closedBall _ _, isCompact_closedBall _ _, ?_, ?_⟩
  · exact fun _ hw ↦ hVL (hballP (closedBall_subset_ball hrP' hw))
  · exact fun _ hw ↦ hVL (hballX (closedBall_subset_ball hrX' hw))

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
