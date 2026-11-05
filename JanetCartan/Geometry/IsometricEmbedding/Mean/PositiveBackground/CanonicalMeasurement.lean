module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationSmooth
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Chart
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalCarrier
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Smoothness of the original canonical preparation measurement

The measurement-chart indicator is redundant on the support of the original
fixed measurement cutoff. Each stress coefficient is extended by that same
cutoff, proving smoothness of the actual operator-valued measurement required
by physical cancellation and preparation. No measurement is reselected.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.PositiveBackground
open ContinuumRow CanonicalCarrier CurrentMean AmplitudeBound
open ActualCarriers FrozenMenu CurrentFullPhase
open ImageGeometry.Periodization

/-- The literal preparation measurement of `CanonicalCarrier.data` is smooth
periodic. Its original stress field is only required on the original physical
domain; the supplied fixed measurement cutoff handles the chart boundary.
Consumers are `physicalDensityMean_uncorrected_core_cancellation_of_supplied_masks`
and `Current.PreparationIteration`
(`app:ch_background:defn:bg-row`, `app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem isSmoothPeriodic_preparationMeasurement_canonical
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (hball : closedBall (0 : Euclidean n) (4 * r) ⊆ U)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ) :
    IsSmoothPeriodic (preparationMeasurement
      (data T Q F row col Φ Y initial hr hcell angular high)) := by
  let d := data T Q F row col Φ Y initial hr hcell angular high
  let q := fun i j k ↦ realPeriodization
    (fun x : Euclidean n ↦ FixedCutoffs.physical hr 1 x * Q.1 x i j k)
  have hentry (i j k : Fin n) : IsSmoothPeriodic (q i j k) := by
    have hQ : ContDiffOn ℝ ∞ (fun x ↦ Q.1 x i j k) (ball (0 : Euclidean n) (4 * r)) :=
      ((Matrix.entryLinearMap ℝ ℝ j k).toContinuousLinearMap.contDiff.comp_contDiffOn
        ((contDiffOn_pi.mp Q.2.1) i)).mono (ball_subset_closedBall.trans hball)
    have hcut : ContDiff ℝ ∞
        (fun x : Euclidean n ↦ FixedCutoffs.physical hr 1 x * Q.1 x i j k) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hx : x ∈ tsupport (FixedCutoffs.physical (n := n) hr 1)
      · apply (FixedCutoffs.physical hr 1).contDiff.contDiffAt.mul
        apply hQ.contDiffAt
        apply isOpen_ball.mem_nhds
        exact (ball_subset_ball (by norm_num; linarith : ((1 : Fin 3) + 2 : ℝ) * r ≤ 4 * r))
          (FixedCutoffs.physical_tsupport hr 1 hx)
      · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport (FixedCutoffs.physical hr 1)).isOpen_compl.mem_nhds hx]
          with y hy
        simp only [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact isSmoothPeriodic_realPeriodization hcell
      ((tsupport_mul_subset_left).trans
        (ImageGeometry.imageCutoff_support_box (FixedCutoffs.physical_tsupport_four hr 1))) hcut
  have hformula (x : Torus n) (B : MetricTensor n) (i : Fin n) :
      preparationMeasurement d x B i = ∑ j, ∑ k, q i j k x * B j k := by
    by_cases hx : x ∈ d.outputChart
    · rw [preparationMeasurement_apply, indicator_of_mem hx]
      change FixedCutoffs.physical hr 1 (centeredTorusRepresentative x) *
        (∑ j, ∑ k, Q.1 (centeredTorusRepresentative x) i j k * B j k) = _
      simp only [q, realPeriodization, Function.comp_apply, Finset.mul_sum, mul_assoc]
    · have hm : FixedCutoffs.periodic hr hcell 1 x = 0 := by
        by_contra h
        exact hx (CommonMeasurement.fixed_measurement_mem_chart hr hcell h)
      rw [preparationMeasurement_apply, indicator_of_notMem hx]
      have hqzero : ∀ j k, q i j k x = 0 := by
        intro j k
        change FixedCutoffs.periodic hr hcell 1 x * Q.1 (centeredTorusRepresentative x) i j k = 0
        rw [hm, zero_mul]
      simp only [hqzero, zero_mul, Finset.sum_const_zero, PiLp.zero_apply]
  have hd : ContDiff ℝ ∞ (periodicLift (preparationMeasurement d)) := by
    apply contDiff_clm_apply_iff.mpr
    intro B
    apply (contDiff_piLp 2).mpr
    intro i
    have he : (fun x : Euclidean n ↦ (periodicLift (preparationMeasurement d) x) B i) =
        fun x ↦ ∑ j, ∑ k, periodicLift (q i j k) x * B j k :=
      funext fun x ↦ hformula (torusQuotient x) B i
    rw [he]
    apply ContDiff.sum
    intro j _
    apply ContDiff.sum
    intro k _
    exact (hentry i j k).2.mul contDiff_const
  have hq : IsOpenQuotientMap (@torusQuotient n) :=
    (IsOpenQuotientMap.piMap (fun _ : Fin n ↦
      QuotientAddGroup.isOpenQuotientMap_mk)).comp
        (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  exact ⟨hq.isQuotientMap.continuous_iff.mpr hd.continuous, hd⟩

end JanetCartan.PositiveBackground
