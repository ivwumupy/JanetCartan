module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PreparedHistory.MeasurementProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.JetFormula

/-!
# The original geometric measurement for the sampled mean

Apply the existing initialized-history measurement producer to its literal
canonical carrier data. The measurement is independent of density, flow and
initial-scalar changes, and agrees across original patches with a common
stress field. On the original fixed plateau it equals the geometric stress
contraction used by the physical mean completion.

Consumers are the same-row canonical run and sampled mean. The actual inverse,
raw and prepared profiles, fine source and corrected event remain separate
producer applications; no bounds for those objects are assumed here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.CurrentMean
open ContinuumRow CanonicalCarrier CorrectedPositiveInverse
  ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame AmplitudeBound

/-- The original measurement does not depend on the background density:
`app:ch_background:eq:bg-affine-mean` changes only the transported normal.
Consumer: the common measurement of the sampled canonical row. -/
theorem preparationMeasurement_correctedCarrierData {n N : ℕ}
    (d : CarrierData n N) (w : CarrierVariable n → ℝ) :
    preparationMeasurement (correctedCarrierData d w) = preparationMeasurement d := rfl

/-- The literal canonical measurement equals the original fixed cutoff times
its supplied stress contraction, including off its output chart
(`app:ch_background:defn:bg-row`). Consumer: the measurement map in
`exists_admissible_history_originalScale_sampledMean_bounds`. -/
theorem preparationMeasurement_canonical_apply
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (x : Torus n) (H : MetricTensor n) (i : Fin n) :
    preparationMeasurement (data T Q F row col Φ Y initial hr hcell angular high) x H i =
      FixedCutoffs.periodic hr hcell 1 x *
        tensorPairing (Q.1 (centeredTorusRepresentative x) i) H := by
  let d := data T Q F row col Φ Y initial hr hcell angular high
  by_cases hx : x ∈ d.outputChart
  · rw [preparationMeasurement_apply, indicator_of_mem hx]
    rfl
  · have hm : FixedCutoffs.periodic hr hcell 1 x = 0 := by
      by_contra h
      exact hx (CommonMeasurement.fixed_measurement_mem_chart hr hcell h)
    rw [preparationMeasurement_apply, indicator_of_notMem hx, hm]
    simp

/-- The measurement already used in preparation is the SAME geometric stress
contraction on its original plateau (`main:eq:mean-equation`,
`app:ch_background:defn:bg-geometry`). No new measurement or chart is chosen. -/
theorem preparationMeasurement_canonical_eq_geometric_on_plateau
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
    (hrank : HasFullNormalRankOn F U) (hQ : Q.1 = projectedStress F)
    (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (hball : closedBall (0 : Euclidean n) (4 * r) ⊆ U)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (w : CarrierVariable n → ℝ) {x : Euclidean n} (hx : x ∈ closedBall 0 (2 * r))
    (H : MetricTensor n) (i : Fin n) :
    preparationMeasurement (correctedCarrierData
      (data T Q F row col Φ Y initial hr hcell angular high) w) (torusQuotient x) H i =
        tensorPairing (StressFrame.geometricCubeStress F x i).val H := by
  have hx4 : x ∈ closedBall (0 : Euclidean n) (4 * r) :=
    closedBall_subset_closedBall (by linarith) hx
  have hxU := hball hx4
  rw [preparationMeasurement_correctedCarrierData,
    preparationMeasurement_canonical_apply,
    PeriodicLocalL2.centeredTorusRepresentative_quotient
      (FixedCutoffs.closedBall_four_subset_cell hcell hx4), hQ]
  have hm : FixedCutoffs.periodic hr hcell 1 (torusQuotient x) = 1 := by
    apply (FixedCutoffs.periodic_eventuallyEq hr hcell 1 hx4).eq_of_nhds.trans
    apply interior_subset (FixedCutoffs.physical_plateau hr 1 ?_)
    convert hx using 1
    norm_num
  rw [hm, one_mul, ImageGeometry.geometricCubeStress_val_eq_projectedStress
    ((hF.contDiffAt (hU.mem_nhds hxU)).of_le (by simp)) (hrank x hxU) i]

/-- All original canonical patches with the same stress field have the same
measurement, despite their distinct flows, scalars and normals. This identifies
only the literal measurement operators, not independent existential choices
(`app:ch_background:defn:bg-row`, `app:ch_mean_pairs:eq:mean-exact-self-change`).
Consumer: the single `C` used by all components of the sampled canonical row. -/
theorem preparationMeasurement_canonical_eq_of_common_stress
    {n N : ℕ} {P₁ P₂ : Patch n} {U₁ U₂ : Set (Euclidean n)}
    {hU₁ : IsOpen U₁} {hU₂ : IsOpen U₂}
    (T₁ : PatchQuantitativeFamily P₁ U₁ hU₁) (T₂ : PatchQuantitativeFamily P₂ U₂ hU₂)
    (Q₁ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U₁ ∧
      cNorm (closedBall (0 : Euclidean n) T₁.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T₁.family.threshold})
    (Q₂ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U₂ ∧
      cNorm (closedBall (0 : Euclidean n) T₂.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T₂.family.threshold})
    (F : Euclidean n → Euclidean N) (row₁ col₁ row₂ col₂ : Fin n)
    (Φ₁ Y₁ Φ₂ Y₂ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial₁ initial₂ : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular₁ angular₂ : CarrierParameter → Euclidean (n - 1) → ℝ) (high₁ high₂ : ℝ → ℝ)
    (w₁ w₂ : CarrierVariable n → ℝ)
    (hQ : EqOn Q₁.1 Q₂.1 (closedBall 0 (4 * r))) :
    preparationMeasurement (correctedCarrierData
      (data T₁ Q₁ F row₁ col₁ Φ₁ Y₁ initial₁ hr hcell angular₁ high₁) w₁) =
    preparationMeasurement (correctedCarrierData
      (data T₂ Q₂ F row₂ col₂ Φ₂ Y₂ initial₂ hr hcell angular₂ high₂) w₂) := by
  simp only [preparationMeasurement_correctedCarrierData]
  funext x
  apply ContinuousLinearMap.ext
  intro H
  ext i
  rw [preparationMeasurement_canonical_apply, preparationMeasurement_canonical_apply]
  by_cases hx : FixedCutoffs.periodic hr hcell 1 x = 0
  · simp only [hx, zero_mul]
  · rw [hQ (CommonMeasurement.fixed_measurement_mem_chart hr hcell hx)]

/-- Apply the initialized-history measurement producer to the exact canonical
operator used by the sampled mean, and identify its geometric contraction on
the original plateau. This discharges `hC`, `hcoef` and `hmeasure` together in
`exists_admissible_history_originalScale_sampledMean_bounds`, with one constant
sequence and threshold before histories. The original source reference, cutoff,
stress, flow, initial scalar and correction density are all retained
(`main:prop:current-scale`, `app:ch_background:defn:bg-row`,
`main:eq:mean-equation`). -/
theorem exists_initialized_history_canonical_measurement_inputs {n : ℕ}
    (G₀ G : FlatReference n) {sourceScale r R : ℝ}
    (hsourceScale : 0 < sourceScale) (hsourceScale₁ : sourceScale ≤ 1)
    (hmap : G.map = sourceDilation G₀.map sourceScale)
    (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (h4rR : 4 * r < R) (hR : R < G₀.domain.chartRadius)
    {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧ ∃ S : ℝ, 2 ≤ S ∧
      ∀ Rinit, S ≤ Rinit →
      ∀ (stage : ℕ) (u : Fin stage → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin stage → ℕ), IsAdmissibleHistory Rinit kMin u ell →
      let F := finiteHistoryMap G.map u
      ContDiff ℝ ∞ F ∧ IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
      ∀ {P : Patch n} (T : PatchQuantitativeFamily P (ball 0 R) isOpen_ball)
        (Q : {Q : Euclidean n → Fin n → MetricTensor n //
          ContDiffOn ℝ ∞ Q (ball 0 R) ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold}),
      Q.1 = projectedStress F →
      ∀ (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
        (w : CarrierVariable n → ℝ),
      let Cmeas := preparationMeasurement (correctedCarrierData
        (data T Q F row col Φ Y initial hr hcell angular high) w)
      IsSmoothPeriodic Cmeas ∧
      (∀ s, cNorm (fundamentalCell n) s (periodicLift Cmeas) ≤
        C s * currentCoefficientScale Rinit stage ^ s) ∧
      ∀ x ∈ closedBall (0 : Euclidean n) (2 * r), ∀ H i,
        Cmeas (torusQuotient x) H i = tensorPairing (StressFrame.geometricCubeStress F x i).val H := by
  obtain ⟨S, hS, κ, _hκ, C, hC, hhistory⟩ :=
    PreparedHistory.exists_initialized_history_preparation_measurement_profiles
      G₀ G hsourceScale hsourceScale₁ hmap hr hcell h4rR hR
      (r₀ := 0) hStar (by omega) horder
  refine ⟨C, hC, S, hS, ?_⟩
  intro Rinit hRinit stage u ell hu F
  obtain ⟨hF, hi, hrank, _hmetric, _hnormal, hfamily⟩ :=
    hhistory Rinit hRinit stage u ell hu
  refine ⟨hF, hi, hrank, ?_⟩
  intro P T Q hQ row col Φ Y initial angular high w Cmeas
  obtain ⟨hCsmooth, hCbound⟩ := hfamily T Q hQ row col Φ Y initial angular high w
  refine ⟨hCsmooth, ?_, ?_⟩
  · simpa only [Nat.sub_zero] using hCbound
  · intro x hx H i
    exact preparationMeasurement_canonical_eq_geometric_on_plateau T Q F hF.contDiffOn
      hrank hQ row col Φ Y initial hr hcell (closedBall_subset_ball h4rR)
      angular high w hx H i

end JanetCartan.CurrentMean
