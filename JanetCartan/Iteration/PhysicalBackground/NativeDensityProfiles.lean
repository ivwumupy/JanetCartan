module

public import JanetCartan.Iteration.PhysicalBackground.NativeSourceProfiles
public import JanetCartan.Iteration.PhysicalBackground.Admission
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import JanetCartan.Iteration.PhysicalBackground.NativeDensityProfilesTemplate

/-!
# High profiles of the unchanged native admitted density

Consumer: `exists_history_retained_normal_coefficient_profiles`, with the
initial reserve Rr = rDensity. The actual source/raw reserve is instantiated at
rDensity + 3 + (n-1) + 2. The exact Fourier label synthesis spends that shift
once; positive square root preserves rDensity. All constants are selected before
the physical history, and the representative is the SAME NativeAdmission.v.
No high-density or successful-inverse conclusion is made into a premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
open JanetCartan JanetCartan.PhysicalBackground JanetCartan.PositiveBackground

namespace JanetCartan.PhysicalBackground

/-- The actual response uses size σ, not an unscaled amplitude bound. Apply the
unit-root profile and retain literal scalar homogeneity without reserve loss. -/
theorem native_positive_initial_profile_scaled
    {n : ℕ} (K : Set (Euclidean (n - 1) × Euclidean 3))
    (σ : ℝ) (hσ : 0 ≤ σ) (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hsmooth : ContDiff ℝ ∞ (fun p ↦ positiveDensityAmplitude 1 (v p)))
    (rDensity : ℕ) (scale : ℝ) (A : ℕ → ℝ)
    (hprofile : HasDerivativeProfile K (fun p ↦ positiveDensityAmplitude 1 (v p)) rDensity scale A) :
    HasDerivativeProfile K (fun p ↦ positiveDensityAmplitude σ (v p)) rDensity scale
      (fun s ↦ σ * A s) := by
  intro s
  have heq : (fun p ↦ positiveDensityAmplitude σ (v p)) =
      σ • (fun p ↦ positiveDensityAmplitude 1 (v p)) := by
    funext p
    simp [positiveDensityAmplitude]
  rw [heq, cNorm_smul σ (hsmooth.of_le (by simp : (s : ℕ∞ω) ≤ ∞)),
    Real.norm_eq_abs, abs_of_nonneg hσ]
  exact (mul_le_mul_of_nonneg_left (hprofile s) hσ).trans_eq (mul_assoc _ _ _).symm

end JanetCartan.PhysicalBackground

realize_native_density_high_profiles
