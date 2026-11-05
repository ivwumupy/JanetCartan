module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.Coordinates

/-!
# Common physical and adapted coefficient buffers

The coefficient estimates use physical closed balls; the flow uses adapted
space-time balls. This inclusion lets the actual construction use the SAME
coefficient bounds for its flow (`app:ch_waves:thm:leading`).
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.NullTransport
open ActualCarriers FrozenMenu CurrentFullPhase ActualFlow FlowAmplitude

/-- A physical coefficient ball contains an adapted state ball centered on
the retained initial section. Both radii are fixed before choosing the frame
(`app:ch_waves:thm:leading`). -/
theorem exists_adapted_coefficient_ball {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    (z : Euclidean 3) (hz : ((0 : Euclidean n), z) ∈ Ω) :
    ∃ ρ R : ℝ, 0 < ρ ∧ 0 < R ∧
      closedBall ((0 : Euclidean n), z) ρ ⊆ Ω ∧
      MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) ρ)
        (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
      MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
        (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
        (closedBall ((0 : Euclidean n), z) ρ) := by
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let W := Ω ∩ Prod.fst ⁻¹' ball (0 : Euclidean n) T.data.localReference.stateRadius
  have hW : IsOpen W := hΩ.inter (isOpen_ball.preimage continuous_fst)
  have hzW : ((0 : Euclidean n), z) ∈ W :=
    ⟨hz, mem_ball_self T.data.localReference.stateRadius_pos⟩
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hzW)
  let ρ := ε / 2
  have hρ : 0 < ρ := half_pos hε
  have hsub : closedBall ((0 : Euclidean n), z) ρ ⊆ W :=
    (closedBall_subset_ball (half_lt_self hε)).trans hb
  let B := ‖C.symm.toContinuousLinearMap‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let R := ρ / B
  have hR : 0 < R := div_pos hρ hB
  refine ⟨ρ, R, hρ, hR, fun _ hw ↦ (hsub hw).1,
    fun _ hw ↦ ball_subset_closedBall (hsub hw).2, ?_⟩
  intro q hq
  have hc : C.symm ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) = (0, z) := by
    simp [C, coordinates_symm_apply]
  rw [mem_closedBall, ← hc, dist_eq_norm, ← map_sub]
  apply (C.symm.toContinuousLinearMap.le_opNorm _).trans
  have hq' : ‖q - ((0 : ℝ), ((0 : Euclidean (n - 1)), z))‖ ≤ R :=
    mem_closedBall_iff_norm.mp hq
  calc
    ‖C.symm.toContinuousLinearMap‖ * ‖q - ((0 : ℝ), ((0 : Euclidean (n - 1)), z))‖ ≤
        ‖C.symm.toContinuousLinearMap‖ * R := mul_le_mul_of_nonneg_left hq' (norm_nonneg _)
    _ ≤ B * R := mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) hR.le
    _ = ρ := mul_div_cancel₀ ρ (ne_of_gt hB)

end JanetCartan.NullTransport
