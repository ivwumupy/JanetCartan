module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PreparedHistory.MeasurementBounds
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.GeometricProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.ScaledReference

/-!
# All-order preparation measurement profiles on the original history

The fixed normalized reference and its larger analytic domain supply the
actual geometric coefficient profile. Applying the literal measurement bound
spends exactly its two-derivative reserve. One threshold and all constants
precede every history, and all derivative orders hold on that same history.
The source scale is already fixed here; no uniformity as it tends to zero is
asserted. The finite source-uniform measurement budgets remain separate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PreparedHistory
open ContinuumRow CanonicalCarrier CurrentMean CorrectedPositiveInverse
  ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
  CurrentCoefficientProfiles ReferenceInitialization

variable {n : ℕ}

/-- Bound the literal measurement on every admissible prefix of the supplied
initialized reference. The larger analytic domain comes from its ORIGINAL
source-dilation identity. The same supplied `Q`, row, column and carrier are
retained, including after background density correction. One threshold works
at every derivative order; high growth is kept as `scale ^ (s - r₀)` after
spending two derivatives. Consumers are the measurement term of
`PreparedDiscrepancy.exists_smoothPreparationDiscrepancy_corrected_tame_bounds`
and Current's rough preparation profiles
(`app:ch_seed:eq:seed-frame-tame`, `app:ch_mean_pairs:prop:mean-coarse`,
`main:prop:current-scale`, `app:eq:uniform-high-coeff`). -/
theorem exists_initialized_history_preparation_measurement_profiles
    (G₀ G : FlatReference n) {sourceScale r R : ℝ}
    (hsourceScale : 0 < sourceScale) (hsourceScale₁ : sourceScale ≤ 1)
    (hmap : G.map = sourceDilation G₀.map sourceScale)
    (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (h4rR : 4 * r < R) (hR : R < G₀.domain.chartRadius)
    {rStar r₀ kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : 2 + r₀ ≤ rStar)
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ κ > (0 : ℝ),
      ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ Rinit, S ≤ Rinit →
      ∀ (stage : ℕ) (u : Fin stage → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin stage → ℕ), IsAdmissibleHistory Rinit kMin u ell →
      let F := finiteHistoryMap G.map u
      ContDiff ℝ ∞ F ∧ IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
      (∀ x ∈ ball (0 : Euclidean n) R, ∀ v,
        (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
      (∀ x ∈ ball (0 : Euclidean n) R, ∀ v ∈ normalSpace F x,
        κ * ‖v‖ ≤ ‖normalPairing F (fun _ ↦ v) x‖) ∧
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
      let d := correctedCarrierData (data T Q F row col Φ Y initial hr hcell angular high) w
      IsSmoothPeriodic (preparationMeasurement d) ∧
      ∀ s, cNorm (fundamentalCell n) s (periodicLift (preparationMeasurement d)) ≤
        C s * currentCoefficientScale Rinit stage ^ (s - r₀) := by
  let Gwide := sourceDilationReference G₀ hsourceScale hsourceScale₁
  have hsame : Gwide.map = G.map := hmap.symm
  obtain ⟨S, hS, _C₀, _hC₀, κ, hκ, _A, Cgeom, _hA, hCgeom, hgeometry⟩ :=
    exists_admissible_history_geometric_profiles Gwide
      (show 0 < 4 * r by positivity) h4rR hR hStar hreserve horder
  choose Cmeas hCmeas hmeasurement using fun s ↦
    exists_canonical_preparation_measurement_cNorm_bound (n := n) hr hcell s
  refine ⟨S, hS, κ, hκ, fun s ↦ Cmeas s * (1 + Cgeom s),
    fun s ↦ mul_pos (hCmeas s) (by linarith [hCgeom s]), ?_⟩
  intro Rinit hRinit stage u ell hu F
  have hgeom := hgeometry Rinit hRinit stage u ell hu
  rw [hsame] at hgeom
  obtain ⟨hi, hrank, _hlow, hmetric, hnormal, _hprofile, hcoeff⟩ := hgeom
  refine ⟨hu.contDiff_finiteHistoryMap G.contDiff, hi, hrank, hmetric, hnormal, ?_⟩
  intro P T Q hQ row col Φ Y initial angular high w d
  refine ⟨(hmeasurement 0 T Q (closedBall_subset_ball h4rR)
    F row col Φ Y initial angular high w).1, ?_⟩
  intro s
  have hsum : (∑ i, cNorm (closedBall (0 : Euclidean n) (4 * r)) s (fun x ↦ Q.1 x i)) ≤
      currentGeometricCoefficientNorm (closedBall 0 (4 * r)) s F := by
    rw [hQ]
    dsimp only [currentGeometricCoefficientNorm]
    have hsecond : 0 ≤ ∑ i, ∑ j,
        cNorm (closedBall (0 : Euclidean n) (4 * r)) s
          (fun x ↦ secondFundamentalForm F x i j) :=
      Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ cNorm_nonneg ..
    linarith [cNorm_nonneg (closedBall (0 : Euclidean n) (4 * r)) s (inducedMetric F),
      cNorm_nonneg (closedBall (0 : Euclidean n) (4 * r)) s (fun x ↦ (inducedMetric F x)⁻¹),
      cNorm_nonneg (closedBall (0 : Euclidean n) (4 * r)) s
        (fun x ↦ (AmbientResponse.canonicalNormalCompletion F x).toContinuousLinearMap)]
  have hbound := (hmeasurement s T Q (closedBall_subset_ball h4rR)
    F row col Φ Y initial angular high w).2
  apply hbound.trans
  have hh := mul_le_mul_of_nonneg_left (hsum.trans (hcoeff s)) (hCmeas s).le
  have hpower : 0 ≤ currentCoefficientScale Rinit stage ^ (s - r₀) :=
    pow_nonneg (le_trans zero_le_one
      (one_le_currentCoefficientScale (by linarith [hS.trans hRinit]) stage)) _
  have hc := mul_nonneg (hCmeas s).le hpower
  nlinarith only [hh, hc]

end JanetCartan.PreparedHistory
