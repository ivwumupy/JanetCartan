module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.AugmentedReference

/-!
# The fixed output center of the augmented chart

The actual central value stays near its frozen value under primitive frame
closeness. Together with the augmented half-gap this gives an output ball
chosen before the immersion (`bg-Psi`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The actual augmented central value is close to its fixed frozen value.
The tolerance is arbitrary and its primitive frame threshold precedes `Q`;
this supplies the common output center in `bg-Psi`. -/
theorem exists_augmented_center_threshold {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    (k : Euclidean n) {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ‖augmentedTransportGradient (transportPosition T Q)
          (augmentedInputCenter T (z₀ := z₀) (k := k)) -
        frozenAugmentedChart T (augmentedInputCenter T (z₀ := z₀) (k := k))‖ ≤ τ := by
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  let p := augmentedInputCenter T (z₀ := z₀) (k := k)
  let c := (adaptedSliceCoordinates T).equiv
  obtain ⟨r, hr, hrbox⟩ := exists_box_radius T hP hz₀
  obtain ⟨_, hphys, hcarrier⟩ := hrbox r hr le_rfl
  have hcarrier' : closedBall (spectatorCenter z₀) r ×ˢ closedBall (z₀ 0) r ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2) :=
    fun p hp ↦ hcarrier ⟨closedBall_subset_closedBall (by linarith) hp.1,
      closedBall_subset_closedBall (by linarith) hp.2⟩
  obtain ⟨δ, hδ, e, he, hcompare⟩ := exists_frame_comparison_threshold T hP z₀ ηb
    (by linarith) hcarrier' (show 0 < τ / (‖c.symm.toContinuousLinearMap‖ + 1) by positivity)
  refine ⟨δ, hδ, fun Q hQ ↦ ?_⟩
  have hq : (spectatorCenter z₀, ((0 : WithLp 2 (ℝ × Euclidean (n - 1))), (0 : WithLp 2 (ℝ × Euclidean (n - 1)))), (z₀ 0, ηb)) ∈
      closedBall (spectatorCenter z₀) r ×ˢ ((closedBall 0 r ×ˢ closedBall 0 r) ×ˢ
        (closedBall (z₀ 0) r ×ˢ closedBall ηb r)) :=
    ⟨mem_closedBall_self hr.le, ⟨mem_closedBall_self hr.le, mem_closedBall_self hr.le⟩,
      mem_closedBall_self hr.le, mem_closedBall_self hr.le⟩
  have hc := (hcompare Q hQ 0 (by simpa using he.le)).1
  have hb : ‖Comparison.fullChart (current T Q) (spatialCarrier T) 0 (spectatorCenter z₀)
      0 0 (z₀ 0, ηb) - frozenChart (fun s ↦ gradient (dispersion T)
        (spatialCarrier T (spectatorCenter z₀, s))) (z₀ 0, ηb)‖ ≤
      τ / (‖c.symm.toContinuousLinearMap‖ + 1) :=
    (hc (spectatorCenter z₀, ((0 : WithLp 2 (ℝ × Euclidean (n - 1))), (0 : WithLp 2 (ℝ × Euclidean (n - 1)))), (z₀ 0, ηb)) hq).1.le
  let v := frozenChart (fun s ↦ gradient (dispersion T)
    (spatialCarrier T (spectatorCenter z₀, s))) (z₀ 0, ηb)
  have heq : c (transportAveragedGradient (transportPosition T Q) p) =
      Comparison.fullChart (current T Q) (spatialCarrier T) 0 (spectatorCenter z₀) 0 0 (z₀ 0, ηb) := by
    have hh := transportAveragedGradient_eq_fullChart T Q p
    change c (transportAveragedGradient (transportPosition T Q) p) =
      Comparison.fullChart (current T Q) (spatialCarrier T) 0 (spectatorCenter z₀)
        (physicalCoordinates T 0) (physicalCoordinates T 0) (z₀ 0, ηb) at hh
    simpa only [map_zero] using hh
  have hd : ‖augmentedTransportGradient (transportPosition T Q) p - frozenAugmentedChart T p‖ =
      ‖c.symm (c (transportAveragedGradient (transportPosition T Q) p) - v)‖ := by
    rw [map_sub, ContinuousLinearEquiv.symm_apply_apply]
    change ‖((0, 0, transportAveragedGradient (transportPosition T Q) p), spectatorCenter z₀) -
      ((0, 0, c.symm v), spectatorCenter z₀)‖ = _
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self,
      norm_zero, max_eq_right (norm_nonneg _), max_eq_left (norm_nonneg _)]
  rw [hd]
  apply (c.symm.toContinuousLinearMap.le_opNorm _).trans
  rw [heq]
  apply (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans
  calc
    ‖c.symm.toContinuousLinearMap‖ * (τ / (‖c.symm.toContinuousLinearMap‖ + 1)) ≤
        (‖c.symm.toContinuousLinearMap‖ + 1) * (τ / (‖c.symm.toContinuousLinearMap‖ + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = τ := by field_simp

end JanetCartan.ContinuumRow.CanonicalConic
