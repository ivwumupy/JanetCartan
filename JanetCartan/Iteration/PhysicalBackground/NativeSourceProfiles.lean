module

public import JanetCartan.Iteration.PhysicalBackground.NativeSourceGeometry
public import JanetCartan.Iteration.PhysicalBackground.NativeMeanProfiles
public import JanetCartan.Iteration.PhysicalBackground.NativeCoefficientProfiles
public import JanetCartan.Iteration.PhysicalBackground.ResidualProfiles
public import JanetCartan.Iteration.PhysicalBackground.SourceBounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.PhysicalSourceProfiles
public meta import JanetCartan.Iteration.PhysicalBackground.NativeSourceProfilesTemplate

/-!
# Actual measured-source and zero-inverse high profiles

Consumer: the same-density and positive-initial high profiles required by
`app:ch_background:prop:bg-current`. The source is the exact native cutoff-one,
factor-two tangent-plus-whole-chi-mean residual. Neither source/raw smallness nor
any successful high analytic estimate is a premise.

Static prefix38: NativeAdmission's first33, then rSource, rCoeff,
rSource<=rCoeff, 2+rCoeff<=rStar, and rSource+canonicalCarrierLowOrder n<=rStar.
The source/raw/inverse profiles have ABI45: prefix38, the unchanged native
history6, then the NUMERICAL operatorS<=R0 certificate. S=max(nativeS,operatorS)
is exposed before histories so the parent supplies both scale certificates
from one chosen common threshold. The coefficient producer is identical to
NativeCoefficientProfiles on the same Gref/b/R/qext/B/rStar/rCoeff/kMin.

Csource and Craw precede every history. Every exponent uses literal
currentCoefficientScale R0 stage. The current zero estimate's extra exponent
s-(rStar-canonicalCarrierLowOrder n) is retained and dominated by s-rSource;
it is never silently discarded. The scalar inverse and augmented raw inverse
are the two components of that SAME native combined estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 3600000

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
open JanetCartan JanetCartan.PhysicalBackground JanetCartan.PositiveBackground
open JanetCartan.ContinuumRow JanetCartan.ContinuumRow.CanonicalCarrier JanetCartan.GeometricProfile JanetCartan.ProtectedFlow
open JanetCartan.ActualCarriers JanetCartan.ActualCarriers.CurrentFullPhase

open JanetCartan.CarrierSobolev

namespace JanetCartan.PhysicalBackground

/-- Scalar last line for the factor-two Sobolev estimate of the measured
cutoff-one source (`app:ch_background:eq:bg-density-input`). -/
theorem native_measured_grade_line {x y a b t : ℝ} (ha : 0 ≤ a)
    (hx : x ≤ a * y) (hy : y ≤ b * t) : x ≤ (a * b) * t :=
  (hx.trans (mul_le_mul_of_nonneg_left hy ha)).trans_eq (mul_assoc _ _ _).symm

/-- The factor of the physical residual seminorm in the actual source estimate
is nonnegative at each order. -/
theorem native_measured_grade_factor_nonneg (n s : ℕ) :
    0 ≤ 2 * Real.sqrt (s.factorial : ℝ) * Real.sqrt ((sobolevMultiindices n s).card : ℝ) := by
  positivity

/-- Combine the two terms of the actual zero-density inverse bound; no
regularity or smallness is discarded. This is the final numerical operation
in the raw profile for `app:ch_background:prop:bg-current`. -/
theorem native_combined_zero_grades {n : ℕ} {ι : Type*} [Fintype ι]
    (e w : OutputL2 n) (h : AugmentedInput n ι) (T : ℝ) (hT : 1 ≤ T)
    (m d r : ℕ) (hr : r + d ≤ m) (C A : ℕ → ℝ) (hC : ∀ s, 0 ≤ C s) (hA : ∀ s, 0 ≤ A s)
    (hs : ∀ s, (periodicSobolevScale n (Euclidean n)).gradeNorm s e ≤ A s * T ^ (s - r))
    (hz : ∀ s, (periodicSobolevScale n (Euclidean n)).gradeNorm s w +
        (augmentedInputSobolevScale n ι).gradeNorm s h ≤ C s *
        ((periodicSobolevScale n (Euclidean n)).gradeNorm s e + T ^ (s - (m - d)) * ‖e‖)) :
    (∀ s, (periodicSobolevScale n (Euclidean n)).gradeNorm s w +
      (augmentedInputSobolevScale n ι).gradeNorm s h ≤ (C s * (A s + A 0)) * T ^ (s - r)) ∧
    (∀ s, (augmentedInputSobolevScale n ι).gradeNorm s h ≤ (C s * (A s + A 0)) * T ^ (s - r)) ∧
    (∀ s, (periodicSobolevScale n (Euclidean n)).gradeNorm s w ≤ (C s * (A s + A 0)) * T ^ (s - r)) := by
  have h0 : ‖e‖ ≤ A 0 := by
    simpa only [GradedScale.gradeNorm_zero, Nat.zero_sub, pow_zero, mul_one] using hs 0
  have both s := calc
    _ ≤ _ := hz s
    _ ≤ (C s * (A s + A 0)) * T ^ (s - r) := by
      have hp := pow_le_pow_right₀ hT (Nat.sub_le_sub_left (Nat.le_sub_of_add_le hr) s)
      rw [mul_assoc, add_mul]
      apply mul_le_mul_of_nonneg_left _ (hC _)
      apply add_le_add (hs s)
      rw [mul_comm (A 0)]
      exact (mul_le_mul_of_nonneg_left h0 (pow_nonneg (zero_le_one.trans hT) _)).trans
        (mul_le_mul_of_nonneg_right hp (hA _))
  exact ⟨both, fun s ↦ (le_add_of_nonneg_left ((periodicSobolevScale n (Euclidean n)).gradeNorm_nonneg s w)).trans (both s),
    fun s ↦ (le_add_of_nonneg_right ((augmentedInputSobolevScale n ι).gradeNorm_nonneg s h)).trans (both s)⟩

end JanetCartan.PhysicalBackground

realize_native_measured_source_high_profiles
