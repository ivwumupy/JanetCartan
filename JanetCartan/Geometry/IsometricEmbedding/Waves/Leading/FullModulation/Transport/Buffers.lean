module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.Direction

/-! # A fixed full-parameter state buffer

The physical coefficient ball in `app:ch_waves:thm:leading` determines an
adapted state radius before the current immersion or initial datum.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.LeadingWave.FullModulation
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude

/-- A physical product ball around the carrier graph contains a fixed
adapted state ball (`app:ch_waves:thm:leading`). -/
theorem exists_adapted_buffer {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ R > 0, MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)),
        (z₀, T.reference.spatialPatch z₀))) R)
      (closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ) := by
  let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
    (adaptedCoordinates T.data.adapted)
  let p₀ := ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
  let L := ‖C.symm.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  let R := ρ / (1 + L)
  have hR : 0 < R := div_pos hρ (by positivity)
  refine ⟨R, hR, ?_⟩
  intro q hq
  have hcenter : C.symm (0, p₀) = ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) := by
    simp [C, p₀, coordinates_symm_apply]
  change dist (C.symm q) _ ≤ ρ
  rw [← hcenter]
  apply (C.symm.toContinuousLinearMap.lipschitzWith.dist_le_mul q (0, p₀)).trans
  apply (mul_le_mul_of_nonneg_left hq hL).trans
  have heq : (1 + L) * R = ρ := by
    dsimp [R]
    exact mul_div_cancel₀ ρ (by positivity)
  nlinarith

end JanetCartan.LeadingWave.FullModulation
