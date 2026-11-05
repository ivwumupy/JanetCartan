module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.Buffers

/-!
# Retaining the doubled coefficient buffer at cell selection

The original minor patch contains the whole doubled physical coefficient
ball. Its inner ball contains the adapted ODE buffer. These two inclusions
are chosen together before a source scale or a current frame is introduced.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumRow.NormalizedChartFamily
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude

/-- Choose the original coefficient cell with its doubled minor buffer and
its adapted ODE buffer simultaneously. Applied to a patch of
`NormalizedFlowProfiles.exists_actual_null_gaps_with_frozen_minors`, the first
inclusion retains that SAME minor on the whole doubled cell, as required by
`NormalizedFlowProfiles.exists_retained_source_lift_profiles_on_original_cylinder`.
This is an original cell selection, not a claim about a previously selected
radius (`app:ch_waves:thm:leading`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_adapted_double_coefficient_ball {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    (z : Euclidean 3) (hz : ((0 : Euclidean n), z) ∈ Ω) :
    ∃ ρ R : ℝ, 0 < ρ ∧ 0 < R ∧
      closedBall ((0 : Euclidean n), z) (2 * ρ) ⊆ Ω ∧
      MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) (2 * ρ))
        (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
      MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
        (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z)) R)
        (closedBall ((0 : Euclidean n), z) ρ) := by
  obtain ⟨r, _, hr, _, hcell, hx, _⟩ := exists_adapted_coefficient_ball T hΩ z hz
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let B := ‖C.symm.toContinuousLinearMap‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let ρ := r / 2
  let R := ρ / B
  have hρ : 0 < ρ := half_pos hr
  have hR : 0 < R := div_pos hρ hB
  have hdouble : 2 * ρ = r := by dsimp [ρ]; ring
  refine ⟨ρ, R, hρ, hR, ?_, ?_, ?_⟩
  · simpa only [hdouble] using hcell
  · simpa only [hdouble] using hx
  · intro q hq
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

end JanetCartan.ContinuumRow.NormalizedChartFamily
