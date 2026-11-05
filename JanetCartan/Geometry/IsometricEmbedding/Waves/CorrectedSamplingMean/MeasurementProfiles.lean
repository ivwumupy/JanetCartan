module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.CorrectedSamplingMean.NormalData
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PreparedHistory.MeasurementProfiles

/-!
# The original preparation measurement in corrected sampling coordinates

Transfer the actual periodic preparation measurement profiles to the physical
projection of the original coefficient domain. The seminorm constant is
unchanged. Apply the initialized-history producer before varying histories;
no compactness bound is chosen after the measurement has varied.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedMean
open NormalComparison ContinuumRow CanonicalCarrier CurrentMean CorrectedPositiveInverse
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open ReferenceInitialization

/-- Pulling back the SAME periodic measurement to coefficient coordinates
costs no derivative or seminorm constant. Periodicity controls all physical
points, including outside the fundamental cell
(`app:ch_waves:eq:sampling-operator-bounds`, `app:ch_mean_pairs:defn:mean-canonical`). -/
theorem cNorm_periodicMeasurement_fst_le {n : ℕ}
    (C : Torus n → MetricTensor n →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (K : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))) (s : ℕ) :
    cNorm K s (fun w ↦ periodicLift C w.1) ≤
      cNorm (fundamentalCell n) s (periodicLift C) := by
  let pr := ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean 3 × Euclidean (n - 1))
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ sSup_norm_iteratedFDeriv_nonneg (fundamentalCell n) j (periodicLift C))
  intro j _ w _
  have hpr := norm_iteratedFDeriv_comp_linear_on_open_le pr
    (f := periodicLift C) (x := w) isOpen_univ hC.2.contDiffOn (mem_univ _) j
  apply (hpr.trans (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le _ _ _)))).trans
  apply norm_iteratedFDeriv_periodicLift_le C j
  intro x hx
  exact le_csSup
    (bddAbove_norm_iteratedFDeriv (isCompact_fundamentalCell n) (hC.2.of_le (by simp)) le_rfl)
    (mem_image_of_mem _ hx)

/-- The original measurement profile supplies the exact coefficient-domain
premise of `exists_fixedRateNormalData_of_measurement_profiles`, with the same
reserve and history scale (`app:ch_seed:eq:seed-frame-tame`,
`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem periodicMeasurement_hasDerivativeProfile {n : ℕ}
    (C : Torus n → MetricTensor n →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (K : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
    {rpar : ℕ} {L : ℝ} {A : ℕ → ℝ}
    (hprofile : HasDerivativeProfile (fundamentalCell n) (periodicLift C) rpar L A) :
    HasDerivativeProfile K (fun w ↦ periodicLift C w.1) rpar L A :=
  fun j ↦ (cNorm_periodicMeasurement_fst_le C hC K j).trans (hprofile j)

/-- The initialized-history producer supplies the literal measurement input
of the corrected mean uniformly before every history and all derivative orders.
The supplied canonical carrier, density correction, reference, stress and
measurement cutoff are unchanged. The two-derivative reserve is exactly the
one in the actual preparation producer (`app:ch_seed:eq:seed-frame-tame`,
`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_initialized_history_sampling_measurement_profiles {n : ℕ}
    (G₀ G : FlatReference n) {sourceScale r R : ℝ}
    (hsourceScale : 0 < sourceScale) (hsourceScale₁ : sourceScale ≤ 1)
    (hmap : G.map = sourceDilation G₀.map sourceScale)
    (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (h4rR : 4 * r < R) (hR : R < G₀.domain.chartRadius)
    {rStar rpar kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : 2 + rpar ≤ rStar)
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ A : ℕ → ℝ, (∀ s, 0 < A s) ∧
      ∀ Rinit, S ≤ Rinit →
      ∀ (stage : ℕ) (u : Fin stage → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin stage → ℕ), IsAdmissibleHistory Rinit kMin u ell →
      let F := finiteHistoryMap G.map u
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
      let C := preparationMeasurement (correctedCarrierData
        (data T Q F row col Φ Y initial hr hcell angular high) w)
      IsSmoothPeriodic C ∧ ∀ K : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))),
        HasDerivativeProfile K (fun q ↦ periodicLift C q.1) rpar
          (currentCoefficientScale Rinit stage) A := by
  obtain ⟨S, hS, _gap, _hgap, A, hA, hprofiles⟩ :=
    PreparedHistory.exists_initialized_history_preparation_measurement_profiles
      G₀ G hsourceScale hsourceScale₁ hmap hr hcell h4rR hR hStar hreserve horder
  refine ⟨S, hS, A, hA, ?_⟩
  intro Rinit hRinit stage u ell hu F P T Q hQ row col Φ Y initial angular high w C
  obtain ⟨_hF, _hi, _hrank, _hmetric, _hnormal, hmeasurement⟩ :=
    hprofiles Rinit hRinit stage u ell hu
  obtain ⟨hC, hbound⟩ := hmeasurement T Q hQ row col Φ Y initial angular high w
  exact ⟨hC, fun K ↦ periodicMeasurement_hasDerivativeProfile C hC K hbound⟩

end JanetCartan.Sampling.CorrectedMean
