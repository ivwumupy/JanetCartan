module

public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearProfilesTemplate

/-!
# Original mean source: the same positive-current linear inverse

The current inverse is constructed from the actual admitted positive density.
All scale constants precede the physical history. Carrier truncation acts only
on the original leading input and never on the image/exterior channels.

Consumer: `fixedSourceLinear` for the finite Picard/source-precision construction
(`new:sec:mean-source-equation`, `new:eq:source-bound`). The later corrected-row
realization and same-event deviation are distinct actual parent applications.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalMeanLinearProfiles
open ContinuumRow CurrentMean CarrierSobolev ContinuumCommutator

/-- Keep the entire fixed source reserve when evaluating the actual positive
initial/map profiles at the native inverse's shifted coefficient order. The
original image ball is a subset of the original map ball; no norm domain is
reselected (`new:eq:source-bound`). -/
theorem retained_source_profile_of_original_profiles
    {n N : ℕ} {ι : Type*} [Fintype ι]
    {K Kimage : Set (Euclidean n)} (hK : IsCompact K) (himage : Kimage ⊆ K)
    (Kin : ι → Set (Euclidean (n-1) × Euclidean 3))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (initial : ι → Euclidean (n-1) × Euclidean 3 → ℝ)
    {rMap rScalar rSource shift : ℕ}
    (hmapReserve : rSource + shift ≤ rMap)
    (hscalarReserve : rSource + shift ≤ rScalar)
    {T : ℝ} (hT : 1 ≤ T)
    (Amap : ℕ → ℝ) (hAmap : ∀ j, 0 ≤ Amap j)
    (Ascalar : ι → ℕ → ℝ) (hAscalar : ∀ i j, 0 ≤ Ascalar i j)
    (hmap : HasDerivativeProfile K F rMap T Amap)
    (hscalar : ∀ i, HasDerivativeProfile (Kin i) (initial i) rScalar T (Ascalar i))
    (s : ℕ) :
    1 + retainedCoefficientProfile K Kimage Kin F initial (s+shift) ≤
      (1 + 2*Amap (s+shift) + ∑ i, Ascalar i (s+shift))*T^(s-rSource) := by
  have hpm : T^(s+shift-rMap) ≤ T^(s-rSource) := pow_le_pow_right₀ hT (by omega)
  have hps : T^(s+shift-rScalar) ≤ T^(s-rSource) := pow_le_pow_right₀ hT (by omega)
  have hm := (hmap (s+shift)).trans (mul_le_mul_of_nonneg_left hpm (hAmap _))
  have hi := (cNorm_mono_set himage hK (hF.of_le (by simp : (↑(s+shift) : ℕ∞ω) ≤ ∞))).trans hm
  have hs : (∑ i, cNorm (Kin i) (s+shift) (initial i)) ≤
      (∑ i, Ascalar i (s+shift))*T^(s-rSource) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦
      (hscalar i (s+shift)).trans (mul_le_mul_of_nonneg_left hps (hAscalar i _))
  have hone := one_le_pow₀ hT (n := s-rSource)
  unfold retainedCoefficientProfile
  linarith

/-- Absorb the genuine retained coefficient profile in the paired CURRENT
inverse estimate. The highest source norm has no positive scale factor.
This arithmetic is applied below to the actual native paired producer, not a
premise about the desired mean output (`new:eq:source-bound`). -/
theorem paired_source_profile_of_retained
    {n : ℕ} {ι : Type*} [Fintype ι]
    (A : AugmentedInput n ι →L[ℝ] OutputL2 n)
    (Q0 : OutputL2 n →L[ℝ] OutputL2 n)
    (H Cpair Ccoef : ℕ → ℝ) (hCpair : ∀ s, 0 ≤ Cpair s) (hCcoef : ∀ s, 0 ≤ Ccoef s)
    {T : ℝ} (hT : 1 ≤ T) (rSource shift : ℕ)
    (hcoef : ∀ s, 1+H (s+shift) ≤ Ccoef s*T^(s-rSource))
    (hpair : ∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
      (periodicSobolevScale n (Euclidean n)).gradeNorm s (Q0 w) +
        (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint (Q0 w)) ≤
      Cpair s*((periodicSobolevScale n (Euclidean n)).gradeNorm s w + (1+H (s+shift))*‖w‖))
    (s : ℕ) (w : OutputL2 n) (hw : w ∈ periodicSobolevLevel n (Euclidean n) s) :
    (periodicSobolevScale n (Euclidean n)).gradeNorm s (Q0 w) +
      (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint (Q0 w)) ≤
    (Cpair s*(1+Ccoef s))*
      ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + T^(s-rSource)*‖w‖) := by
  apply (hpair s w hw).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hCpair s)
  have hc := mul_le_mul_of_nonneg_right (hcoef s) (norm_nonneg w)
  have ha := mul_nonneg (hCcoef s) ((periodicSobolevScale n (Euclidean n)).gradeNorm_nonneg s w)
  have hb := mul_nonneg (pow_nonneg (zero_le_one.trans hT) (s-rSource)) (norm_nonneg w)
  nlinarith

/-- Project the genuine raw half of the paired estimate on smooth sources,
without assuming any tail estimate (`new:sec:mean-source-equation`). -/
theorem raw_source_profile_of_pair {n : ℕ} {ι : Type*} [Fintype ι]
    (A : AugmentedInput n ι →L[ℝ] OutputL2 n) (Q0 : OutputL2 n →L[ℝ] OutputL2 n)
    (C : ℕ → ℝ) (T : ℝ) (r : ℕ)
    (hp : ∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
      (periodicSobolevScale n (Euclidean n)).gradeNorm s (Q0 w) +
        (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint (Q0 w)) ≤
      C s*((periodicSobolevScale n (Euclidean n)).gradeNorm s w + T^(s-r)*‖w‖))
    (s : ℕ) (e : SmoothResidual n) :
    (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint (Q0 (smoothResidualToL2 n e))) ≤
      C s*(residualSobolevSeminorm n s e+T^(s-r)*residualSobolevSeminorm n 0 e) := by
  have h := (le_add_of_nonneg_left
    ((periodicSobolevScale n (Euclidean n)).gradeNorm_nonneg s (Q0 (smoothResidualToL2 n e)))).trans
    (hp s (smoothResidualToL2 n e) (smoothResidualToL2_mem e s))
  simpa only [← residualSobolevSeminorm_eq_gradeNorm, ← residualSobolevSeminorm_zero] using h

/-- Convert the other half of the same positive-current paired estimate to
its actual Fourier Sobolev norm (`app:ch_mean_pairs:eq:block-normal`). -/
theorem inverse_source_profile_of_pair {n : ℕ} {ι : Type*} [Fintype ι]
    (A : AugmentedInput n ι →L[ℝ] OutputL2 n) (Q0 : OutputL2 n →L[ℝ] OutputL2 n)
    (C : ℕ → ℝ) (T : ℝ) (r : ℕ)
    (hQ : ∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
      Q0 w ∈ periodicSobolevLevel n (Euclidean n) s)
    (hp : ∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
      (periodicSobolevScale n (Euclidean n)).gradeNorm s (Q0 w) +
        (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint (Q0 w)) ≤
      C s*((periodicSobolevScale n (Euclidean n)).gradeNorm s w + T^(s-r)*‖w‖))
    (s : ℕ) (w : OutputL2 n) (hw : w ∈ periodicSobolevLevel n (Euclidean n) s) :
    periodicSobolevNorm s (Q0 w) ≤ C s*(periodicSobolevNorm s w+T^(s-r)*‖w‖) := by
  have h := (le_add_of_nonneg_right
    ((augmentedInputSobolevScale n ι).gradeNorm_nonneg s (A.adjoint (Q0 w)))).trans (hp s w hw)
  rw [(periodicSobolevScale n (Euclidean n)).gradeNorm_eq (hQ s w hw),
    (periodicSobolevScale n (Euclidean n)).gradeNorm_eq hw] at h
  change periodicSobolevSeminorm s ⟨Q0 w,hQ s w hw⟩ ≤
    C s*(periodicSobolevSeminorm s ⟨w,hw⟩+T^(s-r)*‖w‖) at h
  simpa only [periodicSobolevSeminorm_eq] using h

/-- The paired positive-current estimate gives the source-only normal tail at
EVERY requested order. Only leading carrier inputs are rounded; image and
exterior channels stay uncut (`new:sec:mean-source-equation`). -/
theorem carrier_tail_of_paired_source_profile {n : ℕ} {ι : Type*} [Fintype ι]
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    {M : ℝ} (hM : ‖physicalRow image U‖ ≤ M)
    (C : ℕ → ℝ) (T : ℝ) (r : ℕ)
    (hreg : ∀ (e : SmoothResidual n) (s : ℕ),
      (augmentedRow image U ψ).adjoint ((augmentedNormal image U ψ).inverse (smoothResidualToL2 n e)) ∈
        augmentedInputLevel n ι s)
    (hp : ∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
      (periodicSobolevScale n (Euclidean n)).gradeNorm s ((augmentedNormal image U ψ).inverse w) +
        (augmentedInputSobolevScale n ι).gradeNorm s
          ((augmentedRow image U ψ).adjoint ((augmentedNormal image U ψ).inverse w)) ≤
      C s*((periodicSobolevScale n (Euclidean n)).gradeNorm s w+T^(s-r)*‖w‖))
    (q : ℕ) {K : ℝ} (hK : 1 ≤ K) (e : SmoothResidual n) :
    ‖(augmentedNormal image U ψ-leadingCarrierCutNormal image U ψ K)
      ((augmentedNormal image U ψ).inverse (smoothResidualToL2 n e))‖ ≤
      ((M+‖1-ψ‖)*C q/K^q)*(residualSobolevSeminorm n q e+T^(q-r)*residualSobolevSeminorm n 0 e) := by
  have h := PhysicalNormalInverse.OriginalNormalSourceTail.source_tail_from_native_pair
    image U ψ hM hK e q (hreg e q) (hp q _ (smoothResidualToL2_mem e q))
  rw [← residualSobolevSeminorm_eq_gradeNorm, ← residualSobolevSeminorm_zero] at h
  exact h.trans_eq (by ring)

/-- Exact leading prefix decomposition with the complete uncut auxiliary
normal (`app:ch_background:eq:bg-carrier-tail`). -/
theorem leading_normal_eq_auxiliary_add_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ)) (K : ℝ) :
    leadingCarrierCutNormal image U ψ K = preparationAuxiliaryOutput image ψ +
      ∑ i, (carrierChannel (U i)).comp ((RawCutoffBounds.carrierSquaredCutoff
        (RawInputPartition.roundedCarrierMask n K)).comp (carrierChannel (U i)).adjoint) := by
  apply ContinuousLinearMap.ext
  intro w
  rw [leadingCarrierCutNormal_apply]
  simp only [add_apply, sum_apply, ContinuousLinearMap.comp_apply, carrierRow_apply]

/-- The original real quadrature normalization on each carrier gives the
literal rounded leading normal, without changing the auxiliary part. -/
theorem leading_normal_eq_normalized_mean {n : ℕ} {ι : Type*} [Fintype ι]
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ)) (K : ℝ)
    (E0 : ι → PeriodicLocalL2.EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      PeriodicLocalL2.EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (hOriginal : ∀ i, PeriodicLocalL2.transferOperator ((4 : ℝ) • realOutputCompression (E0 i)) =
      ((2*Real.pi)^(-(n : ℝ)/2))^2 • (carrierChannel (U i)).comp
        ((RawCutoffBounds.carrierSquaredCutoff (RawInputPartition.roundedCarrierMask n K)).comp
          (carrierChannel (U i)).adjoint)) :
    leadingCarrierCutNormal image U ψ K = preparationAuxiliaryOutput image ψ +
      ∑ i, (((2*Real.pi)^(-(n : ℝ)/2))⁻¹)^2 •
        PeriodicLocalL2.transferOperator ((4 : ℝ) • realOutputCompression (E0 i)) := by
  rw [leading_normal_eq_auxiliary_add_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hOriginal, smul_smul, ← mul_pow,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos (by positivity) _).ne', one_pow, one_smul]

/-- Sum the genuine original colored transport estimates after the exact
Fourier normalization. The unresolved analytic input is precisely the existing
FullComparison output, never a desired E estimate or an event mean cap. -/
theorem corrected_transport_of_original_comparisons {n : ℕ} {ι : Type*} [Fintype ι]
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ)) (K : ℝ)
    (E E0 : ι → PeriodicLocalL2.EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      PeriodicLocalL2.EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (hOriginal : ∀ i, PeriodicLocalL2.transferOperator ((4 : ℝ) • realOutputCompression (E0 i)) =
      ((2*Real.pi)^(-(n : ℝ)/2))^2 • (carrierChannel (U i)).comp
        ((RawCutoffBounds.carrierSquaredCutoff (RawInputPartition.roundedCarrierMask n K)).comp
          (carrierChannel (U i)).adjoint))
    (Ccompare : ι → ℝ) (lam Λ h : ℝ)
    (hCompare : ∀ i, ‖(4 : ℝ) • realOutputCompression (E i) -
      (4 : ℝ) • realOutputCompression (E0 i)‖ ≤ 4*(Ccompare i*lam⁻¹*Λ/h)) :
    ‖leadingCarrierCutNormal image U ψ K -
      (preparationAuxiliaryOutput image ψ + ∑ i, (((2*Real.pi)^(-(n : ℝ)/2))⁻¹)^2 •
        PeriodicLocalL2.transferOperator ((4 : ℝ) • realOutputCompression (E i)))‖ ≤
      (4*(((2*Real.pi)^(-(n : ℝ)/2))⁻¹)^2*(∑ i, Ccompare i))*lam⁻¹*Λ/h := by
  classical
  rw [leading_normal_eq_auxiliary_add_sum, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖(carrierChannel (U i)).comp
        ((RawCutoffBounds.carrierSquaredCutoff (RawInputPartition.roundedCarrierMask n K)).comp
          (carrierChannel (U i)).adjoint) - (((2*Real.pi)^(-(n : ℝ)/2))⁻¹)^2 •
        PeriodicLocalL2.transferOperator ((4 : ℝ) • realOutputCompression (E i))‖ := norm_sum_le ..
    _ ≤ ∑ i, (4*(((2*Real.pi)^(-(n : ℝ)/2))⁻¹)^2*Ccompare i)*lam⁻¹*Λ/h := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [zero_add] using
        (PhysicalNormalInverse.original_corrected_normal_comparison_of_real_transport
          (E i) (E0 i) _ 0 (hOriginal i) (hCompare i))
    _ = _ := by simp only [Finset.sum_div, Finset.sum_mul, Finset.mul_sum]

/-- The native paired reserve already pays the exact three-derivative image
loss; this is only arithmetic, not an auxiliary estimate. -/
theorem auxiliary_reserve {n rStar rSource : ℕ}
    (h : rSource+CanonicalCarrier.canonicalCarrierLowOrder n ≤ rStar) :
    8 ≤ rStar ∧ rSource+3 ≤ rStar := by
  dsimp only [CanonicalCarrier.canonicalCarrierLowOrder] at h
  omega

/-- The same selected coefficient support stays inside its original image
buffer and periodization cell. -/
theorem auxiliary_radius_geometry {μ : ℝ} (hμ : 0 < μ) (hcell : 6*μ < 1/2) :
    0 < 5*μ ∧ 5*μ < 6*μ ∧ 5*μ < 1/2 := by
  constructor
  · positivity
  constructor <;> linarith only [hμ,hcell]

end JanetCartan.PhysicalMean.OriginalMeanLinearProfiles
end

open JanetCartan JanetCartan.CurrentMean JanetCartan.PhysicalMean
construct_original_mean_positive_current
construct_original_mean_current_source_profiles
construct_original_mean_current_prefix
construct_original_mean_auxiliary_profiles
construct_original_mean_low_error_consumer
