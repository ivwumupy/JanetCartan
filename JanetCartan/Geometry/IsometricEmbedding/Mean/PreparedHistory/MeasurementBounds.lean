module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.CanonicalMeasurement
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CorrectedPositiveInverse.SameDensity
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.FiberBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Periodization

/-!
# Bounds for the original preparation measurement

The measurement in the actual finite preparation is the fixed cutoff times
the retained stress contraction, extended by its original chart indicator.
The indicator is redundant on the cutoff support. Expand that same operator
in its finite matrix entries and apply the existing periodization estimates.
The resulting constants precede the frame, immersion, flows and density.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.PreparedHistory
open ContinuumRow CanonicalCarrier CurrentMean AmplitudeBound PositiveBackground
  CorrectedPositiveInverse ActualCarriers FrozenMenu CurrentFullPhase
  ImageGeometry.Periodization FullPhaseCharts.InverseEstimates

variable {n : ℕ}

/-- One fixed matrix-entry contraction in the measurement of
`app:ch_mean_pairs:eq:mean-density-lipschitz`. -/
private def preparationMeasurementEntry (a : Fin n × Fin n × Fin n) :
    ℝ →L[ℝ] (MetricTensor n →L[ℝ] Euclidean n) :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight
    ((Matrix.entryLinearMap ℝ ℝ a.2.1 a.2.2).toContinuousLinearMap.smulRight
      (PiLp.single 2 a.1 1))

/-- The same physical cutoff extends each stress entry smoothly across its
original boundary (`app:ch_background:defn:bg-row`). -/
private theorem contDiff_cut_preparation_entry
    {U : Set (Euclidean n)} (hU : IsOpen U)
    {χ q : Euclidean n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ U) (hq : ContDiffOn ℝ ∞ q U) :
    ContDiff ℝ ∞ (fun x ↦ χ x * q x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hq.contDiffAt (hU.mem_nhds (hs hx)))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- The cutoff-entry derivative estimate uses exactly the original closed
physical buffer, with no derivative loss (`app:ch_background:eq:bg-frame-tame`). -/
private theorem norm_iteratedFDeriv_cut_preparation_entry_le
    {U : Set (Euclidean n)} (hU : IsOpen U) {r : ℝ}
    (hball : closedBall (0 : Euclidean n) r ⊆ U)
    {χ q : Euclidean n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ closedBall (0 : Euclidean n) r)
    (hq : ContDiffOn ℝ ∞ q U) (s : ℕ) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ s (fun y ↦ χ y * q y) x‖ ≤
      cutoffDerivativeBound χ r s * cNorm (closedBall 0 r) s q := by
  by_cases hx : x ∈ tsupport χ
  · have hxr := hs hx
    have hxU := hball hxr
    have hqa (y : Euclidean n) (hy : y ∈ closedBall (0 : Euclidean n) r) :
        ContDiffAt ℝ s q y := (hq.contDiffAt (hU.mem_nhds (hball hy))).of_le (by simp)
    have hp := norm_iteratedFDerivWithin_smul_le hχ.contDiffOn hq
      hU.uniqueDiffOn hxU (n := s) (by simp)
    simp_rw [iteratedFDerivWithin_of_isOpen _ hU hxU] at hp
    apply hp.trans
    calc
      _ ≤ ∑ j ∈ Finset.range (s + 1), (s.choose j : ℝ) *
          cNorm (closedBall 0 r) s χ * cNorm (closedBall 0 r) s q := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall 0 r)
              (hχ.of_le (by simp)) hxr (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
            (Nat.cast_nonneg _)
        · exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall 0 r)
            hqa hxr (Nat.sub_le s j)
        · exact norm_nonneg _
        · exact mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _)
      _ = (∑ j ∈ Finset.range (s + 1), (s.choose j : ℝ) *
          cNorm (closedBall 0 r) s χ) * cNorm (closedBall 0 r) s q :=
        (Finset.sum_mul ..).symm
      _ ≤ cutoffDerivativeBound χ r s * cNorm (closedBall 0 r) s q := by
        apply mul_le_mul_of_nonneg_right _ (cNorm_nonneg _ _ _)
        dsimp only [cutoffDerivativeBound]
        linarith
  · have hz : iteratedFDeriv ℝ s (fun y ↦ χ y * q y) x = 0 := by
      by_contra h
      exact hx (tsupport_mul_subset_left
        (tsupport_iteratedFDeriv_subset s (subset_tsupport _ h)))
    rw [hz, norm_zero]
    exact mul_nonneg (cutoffDerivativeBound_pos χ r s).le (cNorm_nonneg _ _ _)

/-- The original canonical measurement has a fixed linear bound in the same
stress-frame norm. The full physical cutoff and its chart indicator are retained,
including at the fundamental-cell faces. A positive-density correction changes
only the normal amplitude, so the conclusion holds for that SAME corrected
carrier without any estimate on its density. Constants precede all varying
geometry. This discharges the measurement budget and smoothness inputs of
`PreparedPositiveRun.exists_finite_preparation_with_constructed_current` and
`PreparedDiscrepancy.exists_smoothPreparationDiscrepancy_corrected_tame_bounds`
(`app:ch_background:defn:bg-row`, `app:ch_background:eq:bg-frame-tame`,
`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem exists_canonical_preparation_measurement_cNorm_bound
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U},
      ∀ (T : PatchQuantitativeFamily P U hU)
        (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold}),
      closedBall (0 : Euclidean n) (4 * r) ⊆ U →
      ∀ (F : Euclidean n → Euclidean N) (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
        (w : CarrierVariable n → ℝ),
      let d := correctedCarrierData (data T Q F row col Φ Y initial hr hcell angular high) w
      IsSmoothPeriodic (preparationMeasurement d) ∧
      cNorm (fundamentalCell n) s (periodicLift (preparationMeasurement d)) ≤
        C * ∑ i, cNorm (closedBall (0 : Euclidean n) (4 * r)) s (fun x ↦ Q.1 x i) := by
  classical
  let χ := FixedCutoffs.physical (n := n) hr 1
  let cost := ∑ j ∈ Finset.range (s + 1), cutoffDerivativeBound χ (4 * r) j
  have hcost : 0 ≤ cost := Finset.sum_nonneg fun j _ ↦ (cutoffDerivativeBound_pos ..).le
  let entry := fun j k : Fin n ↦ (Matrix.entryLinearMap ℝ ℝ j k).toContinuousLinearMap
  let coefficient := fun a : Fin n × Fin n × Fin n ↦
    ‖preparationMeasurementEntry a‖ * cost * ‖entry a.2.1 a.2.2‖
  have hcoefficient (a) : 0 ≤ coefficient a := by dsimp [coefficient]; positivity
  refine ⟨1 + ∑ a, coefficient a, by positivity, ?_⟩
  intro N P U hU T Q hball F row col Φ Y initial angular high w d
  let q := fun a : Fin n × Fin n × Fin n ↦ fun x : Euclidean n ↦ Q.1 x a.1 a.2.1 a.2.2
  let p := fun a ↦ realPeriodization (fun x ↦ χ x * q a x)
  have hq (a) : ContDiffOn ℝ ∞ (q a) U :=
    (entry a.2.1 a.2.2).contDiff.comp_contDiffOn ((contDiffOn_pi.mp Q.2.1) a.1)
  have hs : tsupport χ ⊆ closedBall (0 : Euclidean n) (4 * r) :=
    FixedCutoffs.physical_tsupport_four hr 1
  have hbox (a) : tsupport (fun x ↦ χ x * q a x) ⊆ {x | ∀ i, |x i| ≤ 4 * r} :=
    tsupport_mul_subset_left.trans
      (ImageGeometry.imageCutoff_support_box (FixedCutoffs.physical_tsupport_four hr 1))
  have hp (a) : IsSmoothPeriodic (p a) :=
    isSmoothPeriodic_realPeriodization hcell (hbox a)
      (contDiff_cut_preparation_entry hU χ.contDiff (hs.trans hball) (hq a))
  have hformula : preparationMeasurement d = fun x ↦
      ∑ a : Fin n × Fin n × Fin n, preparationMeasurementEntry a (p a x) := by
    funext x
    ext H i
    have he : preparationMeasurement d x H i =
        ∑ j, ∑ k, p (i,j,k) x * H j k := by
      by_cases hx : x ∈ d.outputChart
      · rw [preparationMeasurement_apply, indicator_of_mem hx]
        change χ (centeredTorusRepresentative x) *
          (∑ j, ∑ k, Q.1 (centeredTorusRepresentative x) i j k * H j k) = _
        simp only [p, q, realPeriodization, Function.comp_apply, Finset.mul_sum, mul_assoc]
      · have hm : FixedCutoffs.periodic hr hcell 1 x = 0 := by
          by_contra h
          exact hx (CommonMeasurement.fixed_measurement_mem_chart hr hcell h)
        rw [preparationMeasurement_apply, indicator_of_notMem hx]
        change 0 = ∑ j, ∑ k,
          (FixedCutoffs.periodic hr hcell 1 x * Q.1 (centeredTorusRepresentative x) i j k) * H j k
        simp only [hm, zero_mul, Finset.sum_const_zero]
    rw [he]
    simp [preparationMeasurementEntry, Fintype.sum_prod_type, Pi.single_apply, mul_ite]
  have hperiod (a) : cNorm (fundamentalCell n) s (periodicLift (p a)) ≤
      cost * cNorm (closedBall (0 : Euclidean n) (4 * r)) s (q a) := by
    have hh := cNorm_le_sum_of_bounds (s := fundamentalCell n) (r := s)
      (f := periodicLift (p a))
      (C := fun j ↦ cutoffDerivativeBound χ (4 * r) j *
        cNorm (closedBall (0 : Euclidean n) (4 * r)) s (q a))
      (fun j _ ↦ mul_nonneg (cutoffDerivativeBound_pos ..).le (cNorm_nonneg ..))
      (fun j hj x _ ↦ (norm_iteratedFDeriv_realPeriodization_le hcell (hbox a) j
        (norm_iteratedFDeriv_cut_preparation_entry_le hU hball χ.contDiff hs (hq a) j) x).trans
          (mul_le_mul_of_nonneg_left (cNorm_mono_order hj) (cutoffDerivativeBound_pos ..).le))
    simpa only [cost, Finset.sum_mul] using hh
  have hscalar (a) : cNorm (closedBall (0 : Euclidean n) (4 * r)) s (q a) ≤
      ‖entry a.2.1 a.2.2‖ * cNorm (closedBall 0 (4 * r)) s (fun x ↦ Q.1 x a.1) :=
    cNorm_postLinear_le_on (isCompact_closedBall _ _) s (entry a.2.1 a.2.2)
      (fun x hx ↦ (((contDiffOn_pi.mp Q.2.1) a.1).contDiffAt
        (hU.mem_nhds (hball hx))).of_le (by simp))
  have hterm (a) : cNorm (fundamentalCell n) s
      (fun x ↦ preparationMeasurementEntry a (periodicLift (p a) x)) ≤
        coefficient a * ∑ i, cNorm (closedBall (0 : Euclidean n) (4 * r)) s
          (fun x ↦ Q.1 x i) := by
    have hh := (cNorm_postLinear_le_on (isCompact_fundamentalCell n) s
      (preparationMeasurementEntry a) (fun x _ ↦ (hp a).2.contDiffAt.of_le (by simp))).trans
        (mul_le_mul_of_nonneg_left ((hperiod a).trans
          (mul_le_mul_of_nonneg_left (hscalar a) hcost)) (norm_nonneg _))
    have hi := Finset.single_le_sum (fun i _ ↦
      cNorm_nonneg (closedBall (0 : Euclidean n) (4 * r)) s (fun x ↦ Q.1 x i))
      (Finset.mem_univ a.1)
    have hb := mul_le_mul_of_nonneg_left hi (hcoefficient a)
    apply hh.trans
    simpa only [coefficient, mul_assoc] using hb
  refine ⟨isSmoothPeriodic_preparationMeasurement_canonical T Q F row col Φ Y initial
    hr hcell hball angular high, ?_⟩
  rw [hformula]
  change cNorm (fundamentalCell n) s
    (fun x ↦ ∑ a, preparationMeasurementEntry a (periodicLift (p a) x)) ≤ _
  apply (cNorm_sum_le Finset.univ (isCompact_fundamentalCell n)
    (fun a _ ↦ ((preparationMeasurementEntry a).contDiff.comp (hp a).2).of_le (by simp))).trans
  apply (Finset.sum_le_sum (fun a _ ↦ hterm a)).trans
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by linarith) (Finset.sum_nonneg fun i _ ↦ cNorm_nonneg ..)

end JanetCartan.PreparedHistory
