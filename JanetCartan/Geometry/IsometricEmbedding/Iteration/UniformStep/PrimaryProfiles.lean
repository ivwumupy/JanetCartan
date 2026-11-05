module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampledEstimates
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Density

/-!
# Sobolev synthesis of the literal cut sampled primary

For `main:eq:joint-physical-profile`, place the same individual cut atoms in
the actual Fourier Sobolev space and sum there. This proves the norm bound for
the exact primary used by `SampledStage`, including its square-root weights
and real-quadrature factor. No abstract realization or synthesized norm bound
is assumed. The corrected atoms and their individual profiles remain with
`both-corrected-atoms`, specialized to the final measures of `both-current-mean`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.UniformStep

variable {n N : ℕ} {ι : Type*} [Fintype ι]

private theorem sobolev_weighted_sum_le (r : ℕ) (f : ι → Torus n → Euclidean N)
    (hf : ∀ i, IsSmoothPeriodic (f i)) (a : ι → ℝ) (b : ℝ)
    (ha : ∀ i, 0 ≤ a i) {C : ℝ} (hbound : ∀ i, periodicSobolevNorm r (f i) ≤ C) :
    periodicSobolevNorm r (b • ∑ i, a i • f i) ≤ |b| * ((∑ i, a i) * C) := by
  let v (i : ι) := PeriodicSobolevSpace.ofSmooth r (f i) (hf i)
  let w := b • ∑ i, a i • v i
  have hv (i : ι) : ‖v i‖ = periodicSobolevNorm r (f i) := by
    rw [PeriodicSobolevSpace.norm_eq]
    simp only [v, periodicSobolevNorm,
      periodicFourierCoeff_congr_ae (PeriodicSobolevSpace.toL2_ofSmooth_ae _ _ _)]
  have he : (PeriodicSobolevSpace.toL2 r w : Torus n → Euclidean N) =ᵐ[volume]
      b • ∑ i, a i • f i := by
    simp only [w, map_smul, map_sum]
    have hi (i : ι) :
        (a i • PeriodicSobolevSpace.toL2 r (v i) : PeriodicL2 n (Euclidean N)) =ᵐ[volume]
          a i • f i :=
      (Lp.coeFn_smul _ _).trans
        ((PeriodicSobolevSpace.toL2_ofSmooth_ae r (f i) (hf i)).const_smul (a i))
    filter_upwards [Lp.coeFn_smul b (∑ i, a i • PeriodicSobolevSpace.toL2 r (v i)),
      Lp.coeFn_finsetSum Finset.univ (fun i ↦ a i • PeriodicSobolevSpace.toL2 r (v i)),
      Filter.eventually_all.mpr hi] with x hx hsum hix
    simp only [hx, Pi.smul_apply, hsum, Finset.sum_apply]
    congr 1
    exact Finset.sum_congr rfl (fun i _ ↦ hix i)
  have hw : ‖w‖ = periodicSobolevNorm r (b • ∑ i, a i • f i) := by
    rw [PeriodicSobolevSpace.norm_eq]
    simp only [periodicSobolevNorm, periodicFourierCoeff_congr_ae he]
  rw [← hw]
  change ‖b • ∑ i, a i • v i‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (WeightedFamily.norm_sum_weight_smul_le_of_norm_le Finset.univ a
      (fun i _ ↦ ha i) v (fun i _ ↦ (hv i).trans_le (hbound i))) (abs_nonneg b)

set_option maxHeartbeats 600000 in
/-- `main:eq:joint-physical-profile` for the same real primary and the same
physical cutoff as `identities_sampled_history_fields`. The individual cut
atom bounds and sample count/mass imply the complete primary Sobolev profile;
the outside loss is the original fixed `displacementLoss n`, at every order.
Only the local smoothness of the retained atoms is required. -/
theorem cut_sampled_primary_sobolev_le_of_contDiffOn (D : LocalDomain)
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)}
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) (D.chart n)) (r : ℕ)
    {R δ C Ccount Cmass : ℝ} (hR : 1 ≤ R) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hCcount : 0 ≤ Ccount) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass)
    (hatom : ∀ i,
      periodicSobolevNorm r (Periodization.cutToTorus (physicalCutoff D)
        (euclideanRealPart ∘ Z i)) ≤ C * (R ^ carrierExponent) ^ (r : ℝ)) :
    periodicSobolevNorm r (Periodization.cutToTorus (physicalCutoff D)
      (sampledPrimary (δ * R ^ forcingExponent n) μ Z)) ≤
        (Real.sqrt 2 * C * Real.sqrt (Ccount * Cmass)) * δ *
          R ^ displacementLoss n * (R ^ carrierExponent) ^ (r : ℝ) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let f (i : ι) := Periodization.cutToTorus (physicalCutoff D) (euclideanRealPart ∘ Z i)
  have hf (i : ι) : IsSmoothPeriodic (f i) :=
    (physicalCutoff_periodization_of_contDiffOn D
      (euclideanRealPart.contDiff.comp_contDiffOn (hZ i))).1
  have he : Periodization.cutToTorus (physicalCutoff D)
      (sampledPrimary (δ * R ^ forcingExponent n) μ Z) =
        (δ * R ^ forcingExponent n * Real.sqrt 2) • ∑ i, Real.sqrt (μ i) • f i := by
    rw [sampledPrimary, Periodization.cutToTorus_smul]
    apply congrArg ((δ * R ^ forcingExponent n * Real.sqrt 2) • ·)
    funext z
    simp only [Periodization.cutToTorus, Periodization.vectorPeriodization,
      Function.comp_apply, Periodization.cutField, Pi.smul_apply, Finset.sum_apply,
      Finset.smul_sum, f]
    exact Finset.sum_congr rfl (fun i _ ↦ smul_comm _ _ _)
  have hsum := sobolev_weighted_sum_le r f hf (fun i ↦ Real.sqrt (μ i))
    (δ * R ^ forcingExponent n * Real.sqrt 2) (fun _ ↦ Real.sqrt_nonneg _) hatom
  have hw := sampled_weight_sum_le μ hμ hRpos hCcount hCmass hcount hmass
  have hpower : forcingExponent n + (1 + samplingSlack) / 2 ≤ displacementLoss n := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    dsimp [displacementLoss, forcingExponent, meanDerivativeLoss, meanSlack,
      samplingSlack, carrierExponent]
    linarith
  rw [he]
  apply hsum.trans
  rw [abs_of_nonneg (by positivity)]
  calc
    _ ≤ (δ * R ^ forcingExponent n * Real.sqrt 2) *
        ((Real.sqrt (Ccount * Cmass) * R ^ ((1 + samplingSlack) / 2)) *
          (C * (R ^ carrierExponent) ^ (r : ℝ))) := by gcongr
    _ = (Real.sqrt 2 * C * Real.sqrt (Ccount * Cmass)) * δ *
        R ^ (forcingExponent n + (1 + samplingSlack) / 2) *
          (R ^ carrierExponent) ^ (r : ℝ) := by rw [Real.rpow_add hRpos]; ring
    _ ≤ _ := by gcongr

/-- `main:eq:step-L2` for the primary in `SampledStage`: Parseval turns the
proved order-zero synthesis estimate into
`StageConstants.ComponentEstimates.primaryL2` for the same periodic field. -/
theorem cut_sampled_primary_l2_le_of_contDiffOn (D : LocalDomain)
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)}
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) (D.chart n))
    {R δ C Ccount Cmass : ℝ} (hR : 1 ≤ R) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hCcount : 0 ≤ Ccount) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass)
    (hatom : ∀ i, periodicSobolevNorm 0 (Periodization.cutToTorus (physicalCutoff D)
      (euclideanRealPart ∘ Z i)) ≤ C) :
    periodicL2Norm (Periodization.cutToTorus (physicalCutoff D)
      (sampledPrimary (δ * R ^ forcingExponent n) μ Z)) ≤
        (Real.sqrt 2 * C * Real.sqrt (Ccount * Cmass)) * δ * R ^ displacementLoss n := by
  let P := Periodization.cutToTorus (physicalCutoff D)
    (sampledPrimary (δ * R ^ forcingExponent n) μ Z)
  have hP : IsSmoothPeriodic P :=
    (physicalCutoff_periodization_of_contDiffOn D (contDiffOn_sampledPrimary _ μ hZ)).1
  have hz : periodicSobolevNorm 0 P = periodicL2Norm P := by
    simp only [periodicSobolevNorm, Real.rpow_zero, one_mul,
      (hasSum_sq_periodicFourierCoeff_of_continuous hP.1).tsum_eq,
      Real.sqrt_sq (show 0 ≤ periodicL2Norm P from Real.sqrt_nonneg _)]
  have h := cut_sampled_primary_sobolev_le_of_contDiffOn D μ hμ hZ 0 hR hδ hC hCcount hCmass
    hcount hmass (fun i ↦ by simpa only [Nat.cast_zero, Real.rpow_zero, mul_one] using hatom i)
  simpa only [Nat.cast_zero, Real.rpow_zero, mul_one, show periodicSobolevNorm 0
    (Periodization.cutToTorus (physicalCutoff D)
      (sampledPrimary (δ * R ^ forcingExponent n) μ Z)) = periodicL2Norm P from hz] using h

/-- `main:eq:joint-physical-profile`: the original global-smoothness API is
the specialization of the SAME local-field synthesis theorem. -/
theorem cut_sampled_primary_sobolev_le (D : LocalDomain)
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)}
    (hZ : ∀ i, ContDiff ℝ ∞ (Z i)) (r : ℕ)
    {R δ C Ccount Cmass : ℝ} (hR : 1 ≤ R) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hCcount : 0 ≤ Ccount) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass)
    (hatom : ∀ i,
      periodicSobolevNorm r (Periodization.cutToTorus (physicalCutoff D)
        (euclideanRealPart ∘ Z i)) ≤ C * (R ^ carrierExponent) ^ (r : ℝ)) :
    periodicSobolevNorm r (Periodization.cutToTorus (physicalCutoff D)
      (sampledPrimary (δ * R ^ forcingExponent n) μ Z)) ≤
        (Real.sqrt 2 * C * Real.sqrt (Ccount * Cmass)) * δ *
          R ^ displacementLoss n * (R ^ carrierExponent) ^ (r : ℝ) :=
  cut_sampled_primary_sobolev_le_of_contDiffOn D μ hμ (fun i ↦ (hZ i).contDiffOn) r
    hR hδ hC hCcount hCmass hcount hmass hatom

/-- `main:eq:step-L2`: retain the global-smoothness primary API while using
the order-zero estimate for the unchanged physical fields and cutoff. -/
theorem cut_sampled_primary_l2_le (D : LocalDomain)
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)}
    (hZ : ∀ i, ContDiff ℝ ∞ (Z i))
    {R δ C Ccount Cmass : ℝ} (hR : 1 ≤ R) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hCcount : 0 ≤ Ccount) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass)
    (hatom : ∀ i, periodicSobolevNorm 0 (Periodization.cutToTorus (physicalCutoff D)
      (euclideanRealPart ∘ Z i)) ≤ C) :
    periodicL2Norm (Periodization.cutToTorus (physicalCutoff D)
      (sampledPrimary (δ * R ^ forcingExponent n) μ Z)) ≤
        (Real.sqrt 2 * C * Real.sqrt (Ccount * Cmass)) * δ * R ^ displacementLoss n :=
  cut_sampled_primary_l2_le_of_contDiffOn D μ hμ (fun i ↦ (hZ i).contDiffOn)
    hR hδ hC hCcount hCmass hcount hmass hatom

end JanetCartan.UniformStep
