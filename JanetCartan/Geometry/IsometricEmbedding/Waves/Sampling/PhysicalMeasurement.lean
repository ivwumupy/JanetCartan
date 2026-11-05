module
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.CanonicalMeasurement
public import JanetCartan.Geometry.IsometricEmbedding.Waves.CorrectedSamplingMean.MeasurementProfiles
/-!
# The original preparation measurement on the physical sampling chart

The canonical fixed cutoff gives a compact Euclidean representative of the
periodic preparation measurement. Its centered values and all derivatives
retain the original coefficients and seminorm constants. This closes the
physical support input of the corrected sharp-band and common-event estimates.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling
open NormalComparison ContinuumRow CanonicalCarrier CurrentMean CorrectedPositiveInverse
open ActualCarriers FrozenMenu CurrentFullPhase AmplitudeBound

/-- The Euclidean measurement uses the literal original measurement cutoff
and supplied stress field (`app:ch_background:defn:bg-row`). Its values on
centered torus representatives are the preparation measurement. -/
def canonicalSamplingMeasurement {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) {r : ℝ} (hr : 0 < r)
    (x : Euclidean n) : MetricTensor n →L[ℝ] Euclidean n :=
  ({ toFun := fun H ↦ WithLp.toLp 2 (fun i ↦ FixedCutoffs.physical hr 1 x * tensorPairing (Q x i) H)
     map_add' := by
      intro H J
      ext i
      simp [tensorPairing, mul_add, Finset.sum_add_distrib]
     map_smul' := by
      intro a H
      ext i
      simp [tensorPairing, Finset.mul_sum, mul_left_comm] } :
      MetricTensor n →ₗ[ℝ] Euclidean n).toContinuousLinearMap

/-- The original stress contraction and physical cutoff are unchanged
(`app:ch_background:defn:bg-row`). -/
theorem canonicalSamplingMeasurement_apply {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) {r : ℝ} (hr : 0 < r)
    (x : Euclidean n) (H : MetricTensor n) (i : Fin n) :
    canonicalSamplingMeasurement Q hr x H i =
      FixedCutoffs.physical hr 1 x * tensorPairing (Q x i) H := rfl

/-- The physical measurement vanishes with its original cutoff
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem canonicalSamplingMeasurement_eq_zero_of_cutoff_eq_zero {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) {r : ℝ} (hr : 0 < r)
    {x : Euclidean n} (hx : FixedCutoffs.physical hr 1 x = 0) :
    canonicalSamplingMeasurement Q hr x = 0 := by
  ext H i
  simp [canonicalSamplingMeasurement_apply, hx]

/-- Closed physical support is contained in the SAME measurement cutoff,
without introducing a new sampling bump (`app:ch_waves:thm:sampling`). -/
theorem tsupport_canonicalSamplingMeasurement {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) {r : ℝ} (hr : 0 < r) :
    tsupport (canonicalSamplingMeasurement Q hr) ⊆ tsupport (FixedCutoffs.physical hr 1) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra h
  exact hx (canonicalSamplingMeasurement_eq_zero_of_cutoff_eq_zero Q hr (image_eq_zero_of_notMem_tsupport h))

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
local notation "d" => data T Q F row col Φ Y initial hr hcell angular high

/-- The compact Euclidean representative is exactly the original canonical
preparation measurement at every centered representative, including chart
boundaries (`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem canonicalSamplingMeasurement_centered (x : Torus n) :
    canonicalSamplingMeasurement Q.1 hr (centeredTorusRepresentative x) =
      preparationMeasurement d x := by
  ext H i
  rw [canonicalSamplingMeasurement_apply, preparationMeasurement_canonical_apply]
  rfl

/-- The physical and periodic measurements agree on a neighborhood of the
original cutoff support, so all jets agree there
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem canonicalSamplingMeasurement_eventuallyEq {x : Euclidean n}
    (hx : x ∈ tsupport (FixedCutoffs.physical hr 1)) :
    canonicalSamplingMeasurement Q.1 hr =ᶠ[𝓝 x] periodicLift (preparationMeasurement d) := by
  have hx4 : x ∈ ball (0 : Euclidean n) (4 * r) :=
    (ball_subset_ball (by norm_num; linarith : ((1 : Fin 3) + 2 : ℝ) * r ≤ 4 * r))
      (FixedCutoffs.physical_tsupport hr 1 hx)
  filter_upwards [isOpen_ball.mem_nhds hx4] with y hy
  have he := canonicalSamplingMeasurement_centered T Q F row col Φ Y initial hr hcell
    angular high (torusQuotient y)
  rw [PeriodicLocalL2.centeredTorusRepresentative_quotient
    (FixedCutoffs.closedBall_four_subset_cell hcell (ball_subset_closedBall hy))] at he
  exact he

include F row col Φ Y initial hcell angular high in
/-- The original preparation-measurement producer proves smoothness of the
compact sampling measurement; its cutoff handles points outside the chart
(`app:ch_background:defn:bg-row`). -/
theorem contDiff_canonicalSamplingMeasurement
    (hball : closedBall (0 : Euclidean n) (4 * r) ⊆ U) :
    ContDiff ℝ ∞ (canonicalSamplingMeasurement Q.1 hr) := by
  have hC := PositiveBackground.isSmoothPeriodic_preparationMeasurement_canonical
    T Q F row col Φ Y initial hr hcell hball angular high
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (FixedCutoffs.physical hr 1)
  · exact hC.2.contDiffAt.congr_of_eventuallyEq
      (canonicalSamplingMeasurement_eventuallyEq T Q F row col Φ Y initial hr hcell angular high hx)
  · apply (contDiffAt_const (c := (0 : MetricTensor n →L[ℝ] Euclidean n))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    exact canonicalSamplingMeasurement_eq_zero_of_cutoff_eq_zero Q.1 hr hy

/-- The compact physical representative has the original periodic seminorm
budget without a cutoff-product loss (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem cNorm_canonicalSamplingMeasurement_le
    (hball : closedBall (0 : Euclidean n) (4 * r) ⊆ U)
    (K : Set (Euclidean n)) (s : ℕ) :
    cNorm K s (canonicalSamplingMeasurement Q.1 hr) ≤
      cNorm (fundamentalCell n) s (periodicLift (preparationMeasurement d)) := by
  have hC := PositiveBackground.isSmoothPeriodic_preparationMeasurement_canonical
    T Q F row col Φ Y initial hr hcell hball angular high
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ sSup_norm_iteratedFDeriv_nonneg (fundamentalCell n) j
      (periodicLift (preparationMeasurement d)))
  intro j _ x _
  by_cases hx : x ∈ tsupport (FixedCutoffs.physical hr 1)
  · rw [((canonicalSamplingMeasurement_eventuallyEq T Q F row col Φ Y initial hr hcell
      angular high hx).iteratedFDeriv ℝ j).self_of_nhds]
    apply le_csSup
      (bddAbove_norm_iteratedFDeriv (isCompact_fundamentalCell n) (hC.2.of_le (by simp)) le_rfl)
    exact mem_image_of_mem _ (PeriodicLocalL2.halfOpenCell_subset_fundamentalCell
      (FixedCutoffs.closedBall_four_subset_cell hcell (FixedCutoffs.physical_tsupport_four hr 1 hx)))
  · have hz : iteratedFDeriv ℝ j (canonicalSamplingMeasurement Q.1 hr) x = 0 := by
      by_contra h
      exact hx (tsupport_canonicalSamplingMeasurement Q.1 hr
        (tsupport_iteratedFDeriv_subset j (subset_tsupport _ h)))
    rw [hz, norm_zero]
    exact sSup_norm_iteratedFDeriv_nonneg _ _ _

/-- The SAME compact measurement has all original coefficient-coordinate
profiles, with no change of reserve or constant
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem canonicalSamplingMeasurement_hasDerivativeProfile
    (hball : closedBall (0 : Euclidean n) (4 * r) ⊆ U)
    (K : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
    {rpar : ℕ} {L : ℝ} {A : ℕ → ℝ}
    (hprofile : HasDerivativeProfile (fundamentalCell n)
      (periodicLift (preparationMeasurement d)) rpar L A) :
    HasDerivativeProfile K (fun w ↦ canonicalSamplingMeasurement Q.1 hr w.1) rpar L A := by
  intro j
  have hc := contDiff_canonicalSamplingMeasurement T Q F row col Φ Y initial hr hcell
    angular high hball
  let pr := ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean 3 × Euclidean (n - 1))
  apply (cNorm_le_sum_of_bounds
    (fun k _ ↦ sSup_norm_iteratedFDeriv_nonneg (fundamentalCell n) k
      (periodicLift (preparationMeasurement d))) ?_).trans (hprofile j)
  intro k _ w _
  have hp := norm_iteratedFDeriv_comp_linear_on_open_le pr
    (f := canonicalSamplingMeasurement Q.1 hr) (x := w) isOpen_univ
      hc.contDiffOn (mem_univ _) k
  apply (hp.trans (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le _ _ _)))).trans
  change ‖iteratedFDeriv ℝ k (canonicalSamplingMeasurement Q.1 hr) w.1‖ ≤ _
  by_cases hx : w.1 ∈ tsupport (FixedCutoffs.physical hr 1)
  · rw [((canonicalSamplingMeasurement_eventuallyEq T Q F row col Φ Y initial hr hcell
      angular high hx).iteratedFDeriv ℝ k).self_of_nhds]
    have hC := PositiveBackground.isSmoothPeriodic_preparationMeasurement_canonical
      T Q F row col Φ Y initial hr hcell hball angular high
    apply le_csSup
      (bddAbove_norm_iteratedFDeriv (isCompact_fundamentalCell n) (hC.2.of_le (by simp)) le_rfl)
    exact mem_image_of_mem _ (PeriodicLocalL2.halfOpenCell_subset_fundamentalCell
      (FixedCutoffs.closedBall_four_subset_cell hcell (FixedCutoffs.physical_tsupport_four hr 1 hx)))
  · have hz : iteratedFDeriv ℝ k (canonicalSamplingMeasurement Q.1 hr) w.1 = 0 := by
      by_contra h
      exact hx (tsupport_canonicalSamplingMeasurement Q.1 hr
        (tsupport_iteratedFDeriv_subset k (subset_tsupport _ h)))
    rw [hz, norm_zero]
    exact sSup_norm_iteratedFDeriv_nonneg _ _ _

end JanetCartan.Sampling
