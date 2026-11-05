module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationSmooth
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Derivatives.SobolevComparison.Hilbert
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Spectral

/-!
# Carrier integration in the preparation Sobolev estimates

For `app:ch_mean_pairs:eq:mean-density-lipschitz`, differentiate the literal
carrier integral, then apply the existing periodic jet/Sobolev comparison.
Measurable colors remain weights, with no derivatives or number-of-colors
loss. This supplies the integration step for the actual discrepancy; bounds
for the original current and transport atoms remain their producers' inputs.
-/

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
namespace JanetCartan.CurrentMean
open ContinuumRow FiniteChain.Retarded.KernelDecay

variable {n : ℕ} {κ : Type*} [Fintype κ]

/-- Output differentiation commutes with the SAME masked carrier integral.
Compact support and joint smoothness prove all domination requirements; the
color is only measurable (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem iteratedFDeriv_preparationMaskedIntegral
    (mask : CarrierParameter → ℝ) (hm : Measurable mask)
    (hm0 : ∀ z, 0 ≤ mask z) (hm1 : ∀ z, mask z ≤ 1)
    (f : Euclidean n × CarrierParameter → Euclidean n)
    (hf : ContDiff ℝ ∞ f) {K : Set CarrierParameter} (hK : IsCompact K)
    (hs : ∀ x z, z ∉ K → f (x,z) = 0) (j : ℕ) (x : Euclidean n) :
    iteratedFDeriv ℝ j (fun y ↦ ∫ z, mask z • f (y,z) ∂(volume.prod volume)) x =
      ∫ z, mask z • iteratedFDeriv ℝ j (fun y ↦ f (y,z)) x ∂(volume.prod volume) := by
  let μ : Measure CarrierParameter := volume.prod volume
  let ν : Measure CarrierParameter := μ.withDensity (fun z ↦ ENNReal.ofReal (mask z))
  have hν : ν ≤ μ := by
    calc
      _ ≤ μ.withDensity (fun _ ↦ 1) := withDensity_mono
        (ae_of_all _ (fun z ↦ by simpa using ENNReal.ofReal_le_ofReal (hm1 z)))
      _ = μ := withDensity_one
  let : IsFiniteMeasureOnCompacts ν := ⟨fun _ h ↦ lt_of_le_of_lt (hν _) h.measure_lt_top⟩
  have he (y : Euclidean n) : (∫ z, f (y,z) ∂ν) = ∫ z, mask z • f (y,z) ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hm0 _)]
  rw [show (fun y ↦ ∫ z, mask z • f (y,z) ∂μ) =
    (fun y ↦ ∫ z, f (y,z) ∂ν) from funext (fun y ↦ (he y).symm)]
  rw [iteratedFDeriv_integral_commonCarrier hf hK hs,
    integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hm0 _)]
  rfl

/-- Joint smooth sections with common compact support are integrable against
any color in the partition, at every output derivative order. This is an
input-free integrability closure for the preparation bound
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem integrable_preparationMaskedJet
    (mask : CarrierParameter → ℝ) (hm : Measurable mask)
    (hm0 : ∀ z, 0 ≤ mask z) (hm1 : ∀ z, mask z ≤ 1)
    (f : Euclidean n × CarrierParameter → Euclidean n)
    (hf : ContDiff ℝ ∞ f) {K : Set CarrierParameter} (hK : IsCompact K)
    (hs : ∀ x z, z ∉ K → f (x,z) = 0) (j : ℕ) (x : Euclidean n) :
    Integrable (fun z ↦ mask z • iteratedFDeriv ℝ j (fun y ↦ f (y,z)) x)
      (volume.prod volume) := by
  apply (integrable_outputJet_commonCarrier hf hK hs j x).bdd_smul 1 hm.aestronglyMeasurable
  exact ae_of_all _ fun z ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg (hm0 z)] using hm1 z

/-- Order-zero integrability of the SAME masked carrier section. This is
used to subtract two positive-density discrepancies before estimating them
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem integrable_preparationMaskedSection
    (mask : CarrierParameter → ℝ) (hm : Measurable mask)
    (hm0 : ∀ z, 0 ≤ mask z) (hm1 : ∀ z, mask z ≤ 1)
    (f : Torus n × CarrierParameter → Euclidean n) (hc : Continuous f)
    {K : Set CarrierParameter} (hK : IsCompact K)
    (hs : ∀ x z, z ∉ K → f (x,z) = 0) (x : Torus n) :
    Integrable (fun z ↦ mask z • f (x,z)) (volume.prod volume) := by
  have hsupport : HasCompactSupport (fun z ↦ f (x,z)) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    exact closure_minimal (fun z hz ↦ by by_contra hh; exact hz (hs x z hh)) hK.isClosed
  apply (hc.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    hsupport |>.bdd_smul 1 hm.aestronglyMeasurable
  exact ae_of_all _ fun z ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg (hm0 z)] using hm1 z

section Colored

variable (mask : κ → CarrierParameter → ℝ)
    (hm : ∀ c, Measurable (mask c)) (hm0 : ∀ c z, 0 ≤ mask c z)
    (hmask : ∀ z, ∑ c, mask c z = 1)
    (f : κ → Torus n × CarrierParameter → Euclidean n)
    (hc : ∀ c, Continuous (f c))
    (hf : ∀ c, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      f c (torusQuotient p.1,p.2)))
    {K : Set CarrierParameter} (hK : IsCompact K)
    (hs : ∀ c x z, z ∉ K → f c (x,z) = 0)

include hm0 hmask in
private theorem preparationMask_le_one (c : κ) (z : CarrierParameter) : mask c z ≤ 1 :=
  (Finset.single_le_sum (fun a _ ↦ hm0 a z) (Finset.mem_univ c)).trans_eq (hmask z)

include hm hm0 hmask hc hf hK hs

/-- The literal colored carrier integral is smooth. There is no factor
counting colors and no smoothness assumption on their masks
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem isSmoothPeriodic_preparationColoredIntegral :
    IsSmoothPeriodic (fun x ↦ ∫ z, ∑ c, mask c z • f c (x,z) ∂(volume.prod volume)) := by
  have hi (c : κ) (x : Torus n) := integrable_preparationMaskedSection (mask c) (hm c)
    (hm0 c) (preparationMask_le_one mask hm0 hmask c) (f c) (hc c) hK (hs c) x
  have hsm (c : κ) := isSmoothPeriodic_preparationMaskedIntegral (mask c) (hm c)
    (hm0 c) (preparationMask_le_one mask hm0 hmask c) (f c) (hc c) (hf c) hK (hs c)
  simp_rw [integral_finsetSum _ (fun c _ ↦ hi c _)]
  exact ⟨continuous_finsetSum _ (fun c _ ↦ (hsm c).1), ContDiff.sum (fun c _ ↦ (hsm c).2)⟩

/-- Output jets pass through the literal colored integral, retaining the
partition inside the integral (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem iteratedFDeriv_preparationColoredIntegral (j : ℕ) (x : Euclidean n) :
    iteratedFDeriv ℝ j (fun y ↦ ∫ z, ∑ c, mask c z • f c (torusQuotient y,z)
      ∂(volume.prod volume)) x =
      ∫ z, ∑ c, mask c z • iteratedFDeriv ℝ j
        (fun y ↦ f c (torusQuotient y,z)) x ∂(volume.prod volume) := by
  have hi₀ (c : κ) (y : Euclidean n) := integrable_preparationMaskedSection (mask c) (hm c)
    (hm0 c) (preparationMask_le_one mask hm0 hmask c) (f c) (hc c) hK (hs c) (torusQuotient y)
  have hsm (c : κ) := isSmoothPeriodic_preparationMaskedIntegral (mask c) (hm c)
    (hm0 c) (preparationMask_le_one mask hm0 hmask c) (f c) (hc c) (hf c) hK (hs c)
  simp_rw [integral_finsetSum _ (fun c _ ↦ hi₀ c _)]
  rw [iteratedFDeriv_sum]
  · simp only [Finset.sum_apply]
    simp_rw [iteratedFDeriv_preparationMaskedIntegral (mask _) (hm _)
      (hm0 _) (preparationMask_le_one mask hm0 hmask _) _ (hf _) hK
      (fun y z hz ↦ hs _ (torusQuotient y) z hz)]
    exact (integral_finsetSum _ (fun c _ ↦ integrable_preparationMaskedJet (mask c)
      (hm c) (hm0 c) (preparationMask_le_one mask hm0 hmask c) _ (hf c) hK
      (fun y z hz ↦ hs c (torusQuotient y) z hz) j x)).symm
  · intro c _
    exact (hsm c).2.of_le (by simp)

/-- Slice jet bounds give the Sobolev bound for the SAME colored integral.
Only the fixed compact carrier's mass enters, even when the coloring varies
with the mesh (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem periodicSobolevNorm_preparationColoredIntegral_le (s : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ c z, z ∈ K → ∀ j ≤ s, ∀ x : Euclidean n,
      ‖iteratedFDeriv ℝ j (fun y ↦ f c (torusQuotient y,z)) x‖ ≤ B) :
    periodicSobolevNorm s (fun x ↦ ∫ z, ∑ c, mask c z • f c (x,z)
      ∂(volume.prod volume)) ≤
      sobolevPeriodicJetConstant n s * (s + 1 : ℕ) *
        (B * (volume.prod volume).real K) := by
  let g := fun x ↦ ∫ z, ∑ c, mask c z • f c (x,z) ∂(volume.prod volume)
  have hg := isSmoothPeriodic_preparationColoredIntegral mask hm hm0 hmask f hc hf hK hs
  have hmass : 0 ≤ (volume.prod volume : Measure CarrierParameter).real K := ENNReal.toReal_nonneg
  have hjet (j : ℕ) (hj : j ≤ s) (x : Torus n) :
      ‖periodicJet j g x‖ ≤ B * (volume.prod volume).real K := by
    obtain ⟨y, rfl⟩ := exists_torusQuotient_eq x
    change ‖periodicLift (periodicJet j g) y‖ ≤ _
    rw [(periodicJet_spec hg j).2]
    change ‖iteratedFDeriv ℝ j (fun y ↦ ∫ z, ∑ c, mask c z • f c (torusQuotient y,z)
      ∂(volume.prod volume)) y‖ ≤ _
    rw [iteratedFDeriv_preparationColoredIntegral mask hm hm0 hmask f hc hf hK hs]
    have hz₀ : ∀ z ∉ K, (∑ c, mask c z • iteratedFDeriv ℝ j
        (fun y ↦ f c (torusQuotient y,z)) y) = 0 := by
      intro z hz
      apply Finset.sum_eq_zero
      intro c _
      rw [outputJet_eq_zero_off_carrier (f := fun p ↦ f c (torusQuotient p.1,p.2))
        (fun y z hz ↦ hs c (torusQuotient y) z hz) j y hz, smul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz₀]
    let : IsFiniteMeasure ((volume.prod volume : Measure CarrierParameter).restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_ne_top
    apply (norm_integral_le_of_norm_le_const (C := B) ?_).trans_eq
      (by simp only [Measure.real, Measure.restrict_apply_univ])
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact DensityDiscrepancy.norm_masked_sum_le (fun c ↦ mask c z) _
      (fun c ↦ hm0 c z) (hmask z) (fun c ↦ hb c z hz j hj y)
  calc
    _ ≤ sobolevPeriodicJetConstant n s *
        ∑ j ∈ Finset.range (s + 1), periodicL2Norm (periodicJet j g) :=
      periodicSobolevNorm_le_sum_periodicJet_uniform s hg
    _ ≤ sobolevPeriodicJetConstant n s *
        ∑ _j ∈ Finset.range (s + 1), B * (volume.prod volume).real K := by
      apply mul_le_mul_of_nonneg_left _ ((zero_le_one.trans (one_le_sobolevPeriodicJetConstant n s)))
      exact Finset.sum_le_sum fun j hj ↦ periodicL2Norm_le_of_bound _
        (mul_nonneg hB hmass) (hjet j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    _ = _ := by simp [mul_assoc]

/-- Compact-cell slice norms suffice for the preceding global jet bound,
by periodicity. This is the direct input supplied by the current/transport
finite-jet estimates (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem periodicSobolevNorm_preparationColoredIntegral_le_cNorm
    (s : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ c z, z ∈ K →
      cNorm (fundamentalCell n) s (fun y ↦ f c (torusQuotient y,z)) ≤ B) :
    periodicSobolevNorm s (fun x ↦ ∫ z, ∑ c, mask c z • f c (x,z)
      ∂(volume.prod volume)) ≤
      sobolevPeriodicJetConstant n s * (s + 1 : ℕ) *
        (B * (volume.prod volume).real K) := by
  apply periodicSobolevNorm_preparationColoredIntegral_le mask hm hm0 hmask f hc hf hK hs s hB
  intro c z hz j hj x
  have hfz : IsSmoothPeriodic (fun x ↦ f c (x,z)) :=
    ⟨(hc c).comp (continuous_id.prodMk continuous_const),
      (hf c).comp (contDiff_id.prodMk contDiff_const)⟩
  have hjet := norm_periodicJet_le_cNorm hfz j (torusQuotient x)
  change ‖periodicLift (periodicJet j (fun x ↦ f c (x,z))) x‖ ≤ _ at hjet
  rw [(periodicJet_spec hfz j).2] at hjet
  exact hjet.trans ((cNorm_mono_order hj).trans (hb c z hz))

end Colored
end JanetCartan.CurrentMean
