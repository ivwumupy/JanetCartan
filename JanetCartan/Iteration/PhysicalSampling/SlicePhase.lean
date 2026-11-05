module

public import JanetCartan.Iteration.PhysicalSampling.SliceOperator
public import JanetCartan.Iteration.PhysicalSampling.Kernel

/-!
# Exact scalar slice quotient on the retained original phase

Remove the fixed phase/carrier extensions only where the scalar cutoff and
original smooth band are nonzero. The primitive slice buffer and original
shift window give the quotient identity. This matches the constructed sharp
single-channel operator to the SAME physical scalar sampling kernel, without
altering its measure, frequencies, detector or physical cutoff.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalSampling

open ActualCarriers FrozenMenu CurrentFullPhase RawPrimary RawPrimary.SliceBounds RawPrimary.SliceGeometry
open LeadingWave.FullModulation FullPhaseCharts FullPhaseCharts.ActualPhase Sampling.MeasuredAmplitude

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})

/-- Literal phase identity on the fixed scalar support, from the original
quotient segment and SAME retained extension plateaus (`new:eq:amplitude-test`). -/
theorem scalarSlicePhase_eq_retained
    (center : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
    {σ : ℝ} (hσ : 0 < σ) (hphase : closedBall center (2 * σ) ⊆ domain T)
    {a e b : ℝ} (ha : 0 < a) (haR : 4 * a < T.family.radius)
    (he : 0 < e) (heb : 16 * e < b)
    (z : Euclidean 3)
    (hb : ball (T.reference.spatialPatch z) b ⊆
      ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)))
    (hzg : (z, T.reference.spatialPatch z) ∈ closedBall center.2 (σ / 4))
    {ε : ℝ} (hε : ε ∈ Icc 0 e) (hε₀ : ε ≠ 0) (hscale : |ε| ≤ σ / 8)
    (q : ℝ × Euclidean (m + 1 - 1)) (θ : Euclidean (m + 1 - 1))
    (hχa : adaptedPhysicalCoordinates T.data.adapted q ∈ closedBall 0 (a / 4))
    (hχσ : adaptedPhysicalCoordinates T.data.adapted q ∈ closedBall center.1 (σ / 2))
    (hθ : ‖θ‖ ≤ 2) :
    rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z) (ε, q, θ) =
      rawPrimaryPhaseDifference
        (fun q η ↦ extendedRetainedPhase T Q (adaptedPhysicalCoordinates T.data.adapted q) η)
        (extendedRetainedCarrier T center.2.1 hσ z) ε q θ := by
  have hq : q ∈ sliceAdaptedDomain T a :=
    closedBall_subset_ball (by linarith : a / 4 < 4 * a) hχa
  have hε' : ε ∈ sliceParameterDomain e :=
    ⟨by linarith [hε.1], by linarith [hε.2]⟩
  have hθ' : θ ∈ sliceInputExtension (m + 1) :=
    mem_ball_zero_iff.mpr (hθ.trans_lt (by norm_num))
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      T.reference.spatialPatch z + (t * ε) • θ ∈ ball (T.reference.spatialPatch z) b := by
    have hmem : (ε, q, θ) ∈ sliceShiftDomain T a e := ⟨hε', hq, hθ'⟩
    exact (rawSliceShift_mapsTo_sliceShiftDomain T z he heb t
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ hmem).2
  have hqx : adaptedPhysicalCoordinates T.data.adapted q ∈ ball 0 (2 * T.family.radius) :=
    closedBall_subset_ball (by linarith : a / 4 < 2 * T.family.radius) hχa
  have hseg' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      T.reference.spatialPatch z + (t * ε) • θ ∈
        ball (covectorCenter T) (2 * T.family.radius) :=
    ball_subset_ball ((min_le_left _ _).trans (by linarith [T.family.radius_pos])) (hb (hseg t ht))
  rw [show rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z) (ε, q, θ) =
      rawPrimaryPhaseDifference (canonicalBasePhase T Q) (T.reference.spatialPatch z) ε q θ from
    canonicalSlicePhase_eq_div T Q z hqx hε₀ hseg']
  have hzc : z ∈ closedBall center.2.1 σ := by
    have hz := hzg
    rw [← closedBall_prod_same] at hz
    exact closedBall_subset_closedBall (by linarith) hz.1
  rw [extendedRetainedCarrier_eq T center.2.1 hσ hzc]
  have hd : ‖ε • θ‖ ≤ σ / 4 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hscale hθ (norm_nonneg _) (by positivity)).trans_eq (by ring)
  exact (extendedRetainedPhase_difference_eq T Q center hσ hphase hχσ hzg ε θ hd).symm

end JanetCartan.PhysicalSampling
