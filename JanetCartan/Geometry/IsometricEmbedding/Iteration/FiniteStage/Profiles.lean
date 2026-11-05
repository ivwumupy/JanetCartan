module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.FiniteStage.Profiles.SpectralTail
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.FiniteStage.Fourier

/-!
# Finite-stage consequences of physical Sobolev profiles

From the actual smooth periodic fields in `main:eq:joint-physical-profile`,
sharp Fourier interpolation supplies the derivative premises `hDP`, `hDW`
and the final cutoff premise `htail` of
`FiniteStage.correction_of_component_estimates`. Only finitely many Sobolev
orders are needed. The physical-frequency and Hilbert norms are the shared
unit-torus conventions; no wave construction or Sobolev representative is assumed.
-/

@[expose] public noncomputable section

namespace JanetCartan.FiniteStage

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
private theorem derivative_le_cOneNorm {f : Torus n → F} (hf : IsSmoothPeriodic f)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (periodicLift f) x‖ ≤ cNorm (fundamentalCell n) 1 (periodicLift f) := by
  simpa only [norm_iteratedFDeriv_one] using
    norm_iteratedFDeriv_periodicLift_le f 1
      (fun y hy ↦ norm_iteratedFDeriv_le_cNorm (isCompact_fundamentalCell n)
        (hf.2.of_le (by simp)) hy (Nat.le_refl 1)) x

/-- `main:eq:joint-physical-profile`: orders zero and one fixed `m > 1+n/2`
give the sharp global derivative bound, with the amplitude factor unchanged.
This supplies `hDP` and `hDW` to the finite-stage consumer. -/
theorem derivative_le_sobolevProfile {f : Torus n → F} (hf : IsSmoothPeriodic f)
    {m : ℕ} {Λ C₀ Cₘ A : ℝ} (hm : 1 + (n : ℝ) / 2 < m) (hΛ : 1 ≤ Λ)
    (hzero : periodicSobolevNorm 0 f ≤ C₀ * A)
    (hhigh : periodicSobolevNorm m f ≤ Cₘ * A * Λ ^ (m : ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (periodicLift f) x‖ ≤
      (fourierInterpolationConstant n 1 m * (C₀ + Cₘ)) * A * Λ ^ (1 + (n : ℝ) / 2) := by
  apply (derivative_le_cOneNorm hf x).trans
  simpa only [Nat.cast_one] using cNorm_le_gradedSobolevProfile hf (r := 1)
    (by simpa only [Nat.cast_one] using hm) hΛ hzero hhigh

/-- Final cutoff paragraph of `main:thm:step`: at radius `Λ^(1+ζ)`,
order `s+k` of the physical profile gives the tail profile `Λ^(s-ζk)`.
The cutoff is exactly the one used to define the finite-stage increment. -/
theorem sobolev_cutoffTail_le_profile {f : Torus n → F} (hf : IsSmoothPeriodic f)
    {Λ C A : ℝ} (hΛ : 0 < Λ) (s k : ℕ)
    (hprofile : periodicSobolevNorm (s + k : ℕ) f ≤ C * A * Λ ^ ((s + k : ℕ) : ℝ)) :
    periodicSobolevNorm s (f - periodicCutoff (Λ ^ (1 + cutoffSlack)) f) ≤
      C * A * Λ ^ ((s : ℝ) - cutoffSlack * k) := by
  calc
    _ ≤ ((Λ ^ (1 + cutoffSlack)) ^ k)⁻¹ * periodicSobolevNorm (s + k : ℕ) f :=
      sobolev_cutoffTail_le hf (Real.rpow_pos_of_pos hΛ _) s k
    _ ≤ ((Λ ^ (1 + cutoffSlack)) ^ k)⁻¹ * (C * A * Λ ^ ((s + k : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hprofile (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ.le, ← Real.rpow_neg hΛ.le]
      rw [show Λ ^ (-((1 + cutoffSlack) * (k : ℝ))) *
          (C * A * Λ ^ ((s + k : ℕ) : ℝ)) =
          C * A * (Λ ^ (-((1 + cutoffSlack) * (k : ℝ))) *
            Λ ^ ((s + k : ℕ) : ℝ)) by ring, ← Real.rpow_add hΛ]
      congr 2
      push_cast
      ring

/-- The sharp C¹ tail bound in `main:thm:step`, from just the two input
Sobolev orders `k` and `m+k`, where `m > 1+n/2`. The amplitude is retained,
so this applies separately to the primary and secondary fields. -/
theorem cOneNorm_cutoffTail_le_profile {f : Torus n → F} (hf : IsSmoothPeriodic f)
    {m k : ℕ} {Λ Cₖ Cₘₖ A : ℝ} (hm : 1 + (n : ℝ) / 2 < m) (hΛ : 1 ≤ Λ)
    (hlow : periodicSobolevNorm k f ≤ Cₖ * A * Λ ^ (k : ℝ))
    (hhigh : periodicSobolevNorm (m + k : ℕ) f ≤ Cₘₖ * A * Λ ^ ((m + k : ℕ) : ℝ)) :
    cNorm (fundamentalCell n) 1
        (periodicLift (f - periodicCutoff (Λ ^ (1 + cutoffSlack)) f)) ≤
      (fourierInterpolationConstant n 1 m * (Cₖ + Cₘₖ)) *
        A * Λ ^ (1 + (n : ℝ) / 2 - cutoffSlack * k) := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hzero : periodicSobolevNorm 0 (f - periodicCutoff (Λ ^ (1 + cutoffSlack)) f) ≤
      Cₖ * (A * Λ ^ (-(cutoffSlack * k))) := by
    simpa only [Nat.zero_add, Nat.cast_zero, zero_sub, mul_assoc] using
      sobolev_cutoffTail_le_profile hf hΛ0 0 k (by simpa only [Nat.zero_add] using hlow)
  have hhigh' : periodicSobolevNorm m (f - periodicCutoff (Λ ^ (1 + cutoffSlack)) f) ≤
      Cₘₖ * (A * Λ ^ (-(cutoffSlack * k))) * Λ ^ (m : ℝ) := by
    apply (sobolev_cutoffTail_le_profile hf hΛ0 m k hhigh).trans_eq
    rw [sub_eq_add_neg, Real.rpow_add hΛ0]
    ring
  have h := cNorm_le_gradedSobolevProfile (smooth_cutoffTail hf _) (r := 1)
    (by simpa only [Nat.cast_one] using hm) hΛ hzero hhigh'
  simp only [Nat.cast_one] at h
  apply h.trans_eq
  rw [sub_eq_add_neg, Real.rpow_add hΛ0 (1 + (n : ℝ) / 2) (-(cutoffSlack * k))]
  ring

/-- The pointwise differential version of the final cutoff estimate in
`main:thm:step`, valid on the entire periodic lift. -/
theorem derivative_cutoffTail_le_profile {f : Torus n → F} (hf : IsSmoothPeriodic f)
    {m k : ℕ} {Λ Cₖ Cₘₖ A : ℝ} (hm : 1 + (n : ℝ) / 2 < m) (hΛ : 1 ≤ Λ)
    (hlow : periodicSobolevNorm k f ≤ Cₖ * A * Λ ^ (k : ℝ))
    (hhigh : periodicSobolevNorm (m + k : ℕ) f ≤ Cₘₖ * A * Λ ^ ((m + k : ℕ) : ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (periodicLift (f - periodicCutoff (Λ ^ (1 + cutoffSlack)) f)) x‖ ≤
      (fourierInterpolationConstant n 1 m * (Cₖ + Cₘₖ)) *
        A * Λ ^ (1 + (n : ℝ) / 2 - cutoffSlack * k) :=
  (derivative_le_cOneNorm (smooth_cutoffTail hf _) x).trans
    (cOneNorm_cutoffTail_le_profile hf hm hΛ hlow hhigh)

/-- `main:eq:joint-physical-profile` at the carrier scale: the differential
bound in exactly the exponent convention of `correction_of_component_estimates`.
Use amplitude `a = δ` for the primary field and `a = δ²` for the secondary. -/
theorem stage_derivative_le_profile {f : Torus n → F} (hf : IsSmoothPeriodic f)
    {m : ℕ} {R C₀ Cₘ a : ℝ} (hm : 1 + (n : ℝ) / 2 < m) (hR : 1 ≤ R)
    (hzero : periodicSobolevNorm 0 f ≤ C₀ * a * R ^ displacementLoss n)
    (hhigh : periodicSobolevNorm m f ≤
      Cₘ * a * R ^ displacementLoss n * (R ^ carrierExponent) ^ (m : ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (periodicLift f) x‖ ≤
      (fourierInterpolationConstant n 1 m * (C₀ + Cₘ)) * a *
        R ^ (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hΛ : 1 ≤ R ^ carrierExponent := Real.one_le_rpow hR (by norm_num [carrierExponent])
  have h := derivative_le_sobolevProfile hf hm hΛ
    (A := a * R ^ displacementLoss n) (by simpa only [mul_assoc] using hzero)
    (by simpa only [mul_assoc] using hhigh) x
  apply h.trans_eq
  rw [← Real.rpow_mul hR0.le, Real.rpow_add hR0]
  have hp : 1 + (n : ℝ) / 2 = meanDerivativeLoss n + 1 / 2 := by
    unfold meanDerivativeLoss
    ring
  rw [hp]
  ring

/-- The `hDP` and `hDW` premises of `correction_of_component_estimates`,
proved from orders zero and `m` of `main:eq:joint-physical-profile`.
The secondary bound retains its full factor `δ²`. -/
theorem component_derivative_bounds_of_profiles
    {P W : Torus n → F} (hP : IsSmoothPeriodic P) (hW : IsSmoothPeriodic W)
    {m : ℕ} {R C₀ Cₘ δ : ℝ} (hm : 1 + (n : ℝ) / 2 < m) (hR : 1 ≤ R)
    (hPzero : periodicSobolevNorm 0 P ≤ C₀ * δ * R ^ displacementLoss n)
    (hPhigh : periodicSobolevNorm m P ≤
      Cₘ * δ * R ^ displacementLoss n * (R ^ carrierExponent) ^ (m : ℝ))
    (hWzero : periodicSobolevNorm 0 W ≤ C₀ * δ ^ 2 * R ^ displacementLoss n)
    (hWhigh : periodicSobolevNorm m W ≤
      Cₘ * δ ^ 2 * R ^ displacementLoss n * (R ^ carrierExponent) ^ (m : ℝ)) :
    (∀ x, ‖fderiv ℝ (periodicLift P) x‖ ≤
      (fourierInterpolationConstant n 1 m * (C₀ + Cₘ)) * δ *
        R ^ (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2))) ∧
    (∀ x, ‖fderiv ℝ (periodicLift W) x‖ ≤
      (fourierInterpolationConstant n 1 m * (C₀ + Cₘ)) * δ ^ 2 *
        R ^ (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2))) :=
  ⟨stage_derivative_le_profile hP hm hR hPzero hPhigh,
    stage_derivative_le_profile hW hm hR hWzero hWhigh⟩

/-- The final cutoff paragraph of `main:thm:step` for the very same increment
as the finite-stage consumer. Only orders `k` and `m+k` of each component
are used. The secondary amplitude is absorbed using `0 ≤ δ ≤ 1`. -/
theorem cOneNorm_increment_sub_le_profiles {N : ℕ}
    {P W : Torus n → EuclideanSpace ℝ (Fin N)}
    (hP : IsSmoothPeriodic P) (hW : IsSmoothPeriodic W)
    {m k : ℕ} {R Cₖ Cₘₖ δ : ℝ} (hm : 1 + (n : ℝ) / 2 < m) (hR : 1 ≤ R)
    (hCₖ : 0 ≤ Cₖ) (hCₘₖ : 0 ≤ Cₘₖ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hPlow : periodicSobolevNorm k P ≤
      Cₖ * δ * R ^ displacementLoss n * (R ^ carrierExponent) ^ (k : ℝ))
    (hPhigh : periodicSobolevNorm (m + k : ℕ) P ≤
      Cₘₖ * δ * R ^ displacementLoss n * (R ^ carrierExponent) ^ ((m + k : ℕ) : ℝ))
    (hWlow : periodicSobolevNorm k W ≤
      Cₖ * δ ^ 2 * R ^ displacementLoss n * (R ^ carrierExponent) ^ (k : ℝ))
    (hWhigh : periodicSobolevNorm (m + k : ℕ) W ≤
      Cₘₖ * δ ^ 2 * R ^ displacementLoss n * (R ^ carrierExponent) ^ ((m + k : ℕ) : ℝ)) :
    cNorm (fundamentalCell n) 1
        (periodicLift (increment R P W) - (periodicLift P + periodicLift W)) ≤
      (2 * (fourierInterpolationConstant n 1 m * (Cₖ + Cₘₖ)) * δ) *
        (R ^ displacementLoss n * (R ^ carrierExponent) ^
          (meanDerivativeLoss n + 1 / 2 - cutoffSlack * k)) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hΛ : 1 ≤ R ^ carrierExponent := Real.one_le_rpow hR (by norm_num [carrierExponent])
  have hband : (R ^ carrierExponent) ^ (1 + cutoffSlack) = R ^ bandExponent := by
    rw [← Real.rpow_mul hR0.le, ← scale_windows.2.1]
  have hp := cOneNorm_cutoffTail_le_profile hP hm hΛ (A := δ * R ^ displacementLoss n)
    (by simpa only [mul_assoc] using hPlow) (by simpa only [mul_assoc] using hPhigh)
  have hw := cOneNorm_cutoffTail_le_profile hW hm hΛ (A := δ ^ 2 * R ^ displacementLoss n)
    (by simpa only [mul_assoc] using hWlow) (by simpa only [mul_assoc] using hWhigh)
  rw [hband] at hp hw
  have heq : periodicLift (increment R P W) - (periodicLift P + periodicLift W) =
      -(periodicLift (P - periodicCutoff (R ^ bandExponent) P) +
        periodicLift (W - periodicCutoff (R ^ bandExponent) W)) := by
    funext x
    simp only [increment, periodicCutoff_add hP.1 hW.1, periodicLift,
      Function.comp_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
    abel
  rw [heq, cNorm_neg]
  have hsum := cNorm_add_le (isCompact_fundamentalCell n)
    ((smooth_cutoffTail hP (R ^ bandExponent)).2.of_le (by simp) : ContDiff ℝ 1 _)
    ((smooth_cutoffTail hW (R ^ bandExponent)).2.of_le (by simp) : ContDiff ℝ 1 _)
  apply (hsum.trans (add_le_add hp hw)).trans
  have hδsq : δ ^ 2 ≤ δ := by nlinarith
  have hC : 0 ≤ fourierInterpolationConstant n 1 m * (Cₖ + Cₘₖ) :=
    mul_nonneg (fourierInterpolationConstant_nonneg _ _ _) (add_nonneg hCₖ hCₘₖ)
  have hW' :
      (fourierInterpolationConstant n 1 m * (Cₖ + Cₘₖ)) * (δ ^ 2 * R ^ displacementLoss n) *
          (R ^ carrierExponent) ^ (1 + (n : ℝ) / 2 - cutoffSlack * k) ≤
      (fourierInterpolationConstant n 1 m * (Cₖ + Cₘₖ)) * (δ * R ^ displacementLoss n) *
          (R ^ carrierExponent) ^ (1 + (n : ℝ) / 2 - cutoffSlack * k) := by
    gcongr
  apply (add_le_add le_rfl hW').trans_eq
  have hp : 1 + (n : ℝ) / 2 = meanDerivativeLoss n + 1 / 2 := by
    unfold meanDerivativeLoss
    ring
  rw [hp]
  ring

/-- The exact `htail` premise of `correction_of_component_estimates`, derived
from the component Sobolev profiles and the actual fixed cutoff. -/
theorem increment_derivative_tail_le_profiles {N : ℕ}
    {P W : Torus n → EuclideanSpace ℝ (Fin N)}
    (hP : IsSmoothPeriodic P) (hW : IsSmoothPeriodic W)
    {m k : ℕ} {R Cₖ Cₘₖ δ : ℝ} (hm : 1 + (n : ℝ) / 2 < m) (hR : 1 ≤ R)
    (hCₖ : 0 ≤ Cₖ) (hCₘₖ : 0 ≤ Cₘₖ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hPlow : periodicSobolevNorm k P ≤
      Cₖ * δ * R ^ displacementLoss n * (R ^ carrierExponent) ^ (k : ℝ))
    (hPhigh : periodicSobolevNorm (m + k : ℕ) P ≤
      Cₘₖ * δ * R ^ displacementLoss n * (R ^ carrierExponent) ^ ((m + k : ℕ) : ℝ))
    (hWlow : periodicSobolevNorm k W ≤
      Cₖ * δ ^ 2 * R ^ displacementLoss n * (R ^ carrierExponent) ^ (k : ℝ))
    (hWhigh : periodicSobolevNorm (m + k : ℕ) W ≤
      Cₘₖ * δ ^ 2 * R ^ displacementLoss n * (R ^ carrierExponent) ^ ((m + k : ℕ) : ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (periodicLift (increment R P W) - (periodicLift P + periodicLift W)) x‖ ≤
      (2 * (fourierInterpolationConstant n 1 m * (Cₖ + Cₘₖ)) * δ) *
        (R ^ displacementLoss n * (R ^ carrierExponent) ^
          (meanDerivativeLoss n + 1 / 2 - cutoffSlack * k)) := by
  have hs : IsSmoothPeriodic (increment R P W - (P + W)) :=
    ⟨(isSmoothPeriodic_periodicCutoff _ _).1.sub (hP.1.add hW.1),
      (isSmoothPeriodic_periodicCutoff _ _).2.sub (hP.2.add hW.2)⟩
  exact (derivative_le_cOneNorm hs x).trans
    (cOneNorm_increment_sub_le_profiles hP hW hm hR hCₖ hCₘₖ hδ hδ1 hPlow hPhigh hWlow hWhigh)

end JanetCartan.FiniteStage
