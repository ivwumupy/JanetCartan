module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.OneHigh

/-!
# Actual transport derivatives from primitive one-high profiles

These conditional estimates for `app:ch_regular_base:eq:actual-one-high` apply
the shared derivative budget to the literal amplitudes. No correction or remainder
estimate is an input. The high quantity `H` may be `1 + ‖a‖_{H^{s+β}}` once the
primitive profiles have been obtained from the finite buffered coefficient bounds.
The constants depend only on the primitive profile constants and fixed directions.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.FourierIntegral
variable {E R ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℂ R] [Fintype ι]
local instance : NormedAlgebra ℝ R := NormedAlgebra.restrictScalars ℝ ℂ R

/-- Uncollapsed joint profile for the leading amplitude, consumed by masked
transport bounds in `app:ch_regular_base:eq:actual-one-high`. -/
theorem norm_iteratedFDeriv_leadingAmplitude_profile (n W δ : ℕ)
    {c U : E → R} (hc : ContDiff ℝ n c) (hU : ContDiff ℝ n U)
    {M : ℕ → ℝ} (hM : ∀ k, 0 ≤ M k) {H : ℝ} (hH : 1 ≤ H) (x : E)
    (hcP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k c x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hUP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k U x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W)) :
    ‖iteratedFDeriv ℝ n (fun y ↦ leadingAmplitude (c y) (U y)) x‖ ≤
      transportLeibnizBound M M n * H ^ (((n + (δ + δ) : ℕ) : ℝ) / W) := by
  apply (norm_iteratedFDeriv_leadingAmplitude_le hc hU x n le_rfl).trans
  exact (transportLeibnizBound_profile_le (lt_of_lt_of_le zero_lt_one hH) W δ δ n
    (fun _ _ ↦ norm_nonneg _) (fun k _ ↦ hM k) hcP hUP)

/-- Uncollapsed joint profile for the literal correction, consumed by masked
transport bounds in `app:ch_regular_base:eq:actual-one-high`. -/
theorem norm_iteratedFDeriv_correctionAmplitude_profile (n W δ : ℕ)
    {c1 dU : ι → E → R} {c2 : ι → ι → E → R}
    {S : ι → ι → E → ℂ} {U : E → R}
    (hc1 : ∀ j, ContDiff ℝ n (c1 j)) (hdU : ∀ j, ContDiff ℝ n (dU j))
    (hc2 : ∀ j l, ContDiff ℝ n (c2 j l))
    (hS : ∀ j l, ContDiff ℝ n (S j l)) (hU : ContDiff ℝ n U)
    {M : ℕ → ℝ} (hM : ∀ k, 0 ≤ M k) {H : ℝ} (hH : 1 ≤ H) (x : E)
    (hc1P : ∀ j k, k ≤ n → ‖iteratedFDeriv ℝ k (c1 j) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hdUP : ∀ j k, k ≤ n → ‖iteratedFDeriv ℝ k (dU j) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hc2P : ∀ j l k, k ≤ n → ‖iteratedFDeriv ℝ k (c2 j l) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hSP : ∀ j l k, k ≤ n → ‖iteratedFDeriv ℝ k (S j l) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hUP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k U x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W)) :
    ‖iteratedFDeriv ℝ n (fun y ↦ correctionAmplitude (fun j ↦ c1 j y)
      (fun j ↦ dU j y) (fun j l ↦ c2 j l y) (fun j l ↦ S j l y) (U y)) x‖ ≤
      correctionProfileConstant (ι := ι) M n * H ^ (((n + 3 * δ : ℕ) : ℝ) / W) := by
  apply (norm_iteratedFDeriv_correctionAmplitude_le hc1 hdU hc2 hS hU x n le_rfl).trans
  exact (correctionDerivativeBound_profile_le hH hM W δ n
    (fun j k hk ↦ ⟨norm_nonneg _, hc1P j k hk⟩)
    (fun j k hk ↦ ⟨norm_nonneg _, hdUP j k hk⟩)
    (fun j l k hk ↦ ⟨norm_nonneg _, hc2P j l k hk⟩)
    (fun j l k hk ↦ ⟨norm_nonneg _, hSP j l k hk⟩)
    (fun k hk ↦ ⟨norm_nonneg _, hUP k hk⟩))

/-- Uncollapsed joint profile for the complete remainder, including its actual
spatial derivative and `B b₋₁`. Consumed by masked transport estimates in
`app:ch_regular_base:eq:actual-one-high`. -/
theorem norm_iteratedFDeriv_completeTransportRemainder_profile (n W δ : ℕ)
    {A : ι → E → R} {B : E → R}
    {c1 dU : ι → E → R} {c2 : ι → ι → E → R}
    {S : ι → ι → E → ℂ} {U : E → R}
    (hA : ∀ j, ContDiff ℝ n (A j)) (hB : ContDiff ℝ n B)
    (hc1 : ∀ j, ContDiff ℝ (n + 1) (c1 j)) (hdU : ∀ j, ContDiff ℝ (n + 1) (dU j))
    (hc2 : ∀ j l, ContDiff ℝ (n + 1) (c2 j l))
    (hS : ∀ j l, ContDiff ℝ (n + 1) (S j l)) (hU : ContDiff ℝ (n + 1) U)
    {M : ℕ → ℝ} (hM : ∀ k, 0 ≤ M k) {H : ℝ} (hH : 1 ≤ H) (x : E) (v : ι → E)
    (hAP : ∀ j k, k ≤ n → ‖iteratedFDeriv ℝ k (A j) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hBP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k B x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hc1P : ∀ j k, k ≤ n + 1 → ‖iteratedFDeriv ℝ k (c1 j) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hdUP : ∀ j k, k ≤ n + 1 → ‖iteratedFDeriv ℝ k (dU j) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hc2P : ∀ j l k, k ≤ n + 1 → ‖iteratedFDeriv ℝ k (c2 j l) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hSP : ∀ j l k, k ≤ n + 1 → ‖iteratedFDeriv ℝ k (S j l) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hUP : ∀ k ≤ n + 1, ‖iteratedFDeriv ℝ k U x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W)) :
    let b := fun y ↦ correctionAmplitude (fun j ↦ c1 j y) (fun j ↦ dU j y)
      (fun j l ↦ c2 j l y) (fun j l ↦ S j l y) (U y)
    ‖iteratedFDeriv ℝ n (fun y ↦ transportRemainder (fun j ↦ A j y)
      (fun j ↦ fderiv ℝ b y (v j)) (B y) (b y)) x‖ ≤
      completeRemainderProfileConstant M (fun j ↦ ‖v j‖) n * H ^ (((n + (4 * δ + 1) : ℕ) : ℝ) / W) := by
  intro b
  apply (norm_iteratedFDeriv_completeTransportRemainder_le n hA hB hc1 hdU hc2 hS hU x v).trans
  exact (completeTransportDerivativeBound_profile_le hH hM (fun _ ↦ norm_nonneg _) W δ n
    (fun j k hk ↦ ⟨norm_nonneg _, hAP j k hk⟩)
    (fun k hk ↦ ⟨norm_nonneg _, hBP k hk⟩)
    (fun j k hk ↦ ⟨norm_nonneg _, hc1P j k hk⟩)
    (fun j k hk ↦ ⟨norm_nonneg _, hdUP j k hk⟩)
    (fun j l k hk ↦ ⟨norm_nonneg _, hc2P j l k hk⟩)
    (fun j l k hk ↦ ⟨norm_nonneg _, hSP j l k hk⟩)
    (fun k hk ↦ ⟨norm_nonneg _, hUP k hk⟩))

/-- The leading amplitude spends the high coefficient norm once, with fixed
shift `2δ`, in `app:ch_regular_base:eq:direct-graph-amplitudes`. -/
theorem norm_iteratedFDeriv_leadingAmplitude_oneHigh (n W δ : ℕ)
    {c U : E → R} (hc : ContDiff ℝ n c) (hU : ContDiff ℝ n U)
    {M : ℕ → ℝ} (hM : ∀ k, 0 ≤ M k) {H : ℝ} (hH : 1 ≤ H) (x : E)
    (hbudget : n + 2 * δ ≤ W)
    (hcP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k c x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hUP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k U x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W)) :
    ‖iteratedFDeriv ℝ n (fun y ↦ leadingAmplitude (c y) (U y)) x‖ ≤
      transportLeibnizBound M M n * H := by
  apply (norm_iteratedFDeriv_leadingAmplitude_le hc hU x n le_rfl).trans
  exact (transportLeibnizBound_profile_le (lt_of_lt_of_le zero_lt_one hH) W δ δ n
    (fun _ _ ↦ norm_nonneg _) (fun k _ ↦ hM k) hcP hUP).trans
    (transportProfile_le_oneHigh hH (transportLeibnizBound_nonneg hM hM n) (by omega))

/-- The literal correction has a linear high bound with fixed shift `3δ`.
All inputs are derivative bounds on primitives from
`app:ch_regular_base:eq:direct-graph-amplitudes`, including the phase Hessian. -/
theorem norm_iteratedFDeriv_correctionAmplitude_oneHigh (n W δ : ℕ)
    {c1 dU : ι → E → R} {c2 : ι → ι → E → R}
    {S : ι → ι → E → ℂ} {U : E → R}
    (hc1 : ∀ j, ContDiff ℝ n (c1 j)) (hdU : ∀ j, ContDiff ℝ n (dU j))
    (hc2 : ∀ j l, ContDiff ℝ n (c2 j l))
    (hS : ∀ j l, ContDiff ℝ n (S j l)) (hU : ContDiff ℝ n U)
    {M : ℕ → ℝ} (hM : ∀ k, 0 ≤ M k) {H : ℝ} (hH : 1 ≤ H) (x : E)
    (hbudget : n + 3 * δ ≤ W)
    (hc1P : ∀ j k, k ≤ n → ‖iteratedFDeriv ℝ k (c1 j) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hdUP : ∀ j k, k ≤ n → ‖iteratedFDeriv ℝ k (dU j) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hc2P : ∀ j l k, k ≤ n → ‖iteratedFDeriv ℝ k (c2 j l) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hSP : ∀ j l k, k ≤ n → ‖iteratedFDeriv ℝ k (S j l) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hUP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k U x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W)) :
    ‖iteratedFDeriv ℝ n (fun y ↦ correctionAmplitude (fun j ↦ c1 j y)
      (fun j ↦ dU j y) (fun j l ↦ c2 j l y) (fun j l ↦ S j l y) (U y)) x‖ ≤
      correctionProfileConstant (ι := ι) M n * H := by
  apply (norm_iteratedFDeriv_correctionAmplitude_le hc1 hdU hc2 hS hU x n le_rfl).trans
  exact (correctionDerivativeBound_profile_le hH hM W δ n
    (fun j k hk ↦ ⟨norm_nonneg _, hc1P j k hk⟩)
    (fun j k hk ↦ ⟨norm_nonneg _, hdUP j k hk⟩)
    (fun j l k hk ↦ ⟨norm_nonneg _, hc2P j l k hk⟩)
    (fun j l k hk ↦ ⟨norm_nonneg _, hSP j l k hk⟩)
    (fun k hk ↦ ⟨norm_nonneg _, hUP k hk⟩)).trans
    (transportProfile_le_oneHigh hH (correctionProfileConstant_nonneg hM n) hbudget)

/-- The complete remainder, with the actual derivative of the correction and
with `B b₋₁`, has a linear high bound at fixed shift `4δ+1`. Source:
`app:ch_regular_base:eq:direct-graph-identity` and
`app:ch_regular_base:eq:actual-one-high`. -/
theorem norm_iteratedFDeriv_completeTransportRemainder_oneHigh (n W δ : ℕ)
    {A : ι → E → R} {B : E → R}
    {c1 dU : ι → E → R} {c2 : ι → ι → E → R}
    {S : ι → ι → E → ℂ} {U : E → R}
    (hA : ∀ j, ContDiff ℝ n (A j)) (hB : ContDiff ℝ n B)
    (hc1 : ∀ j, ContDiff ℝ (n + 1) (c1 j)) (hdU : ∀ j, ContDiff ℝ (n + 1) (dU j))
    (hc2 : ∀ j l, ContDiff ℝ (n + 1) (c2 j l))
    (hS : ∀ j l, ContDiff ℝ (n + 1) (S j l)) (hU : ContDiff ℝ (n + 1) U)
    {M : ℕ → ℝ} (hM : ∀ k, 0 ≤ M k) {H : ℝ} (hH : 1 ≤ H) (x : E) (v : ι → E)
    (hbudget : n + (4 * δ + 1) ≤ W)
    (hAP : ∀ j k, k ≤ n → ‖iteratedFDeriv ℝ k (A j) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hBP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k B x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hc1P : ∀ j k, k ≤ n + 1 → ‖iteratedFDeriv ℝ k (c1 j) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hdUP : ∀ j k, k ≤ n + 1 → ‖iteratedFDeriv ℝ k (dU j) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hc2P : ∀ j l k, k ≤ n + 1 → ‖iteratedFDeriv ℝ k (c2 j l) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hSP : ∀ j l k, k ≤ n + 1 → ‖iteratedFDeriv ℝ k (S j l) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hUP : ∀ k ≤ n + 1, ‖iteratedFDeriv ℝ k U x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W)) :
    let b := fun y ↦ correctionAmplitude (fun j ↦ c1 j y) (fun j ↦ dU j y)
      (fun j l ↦ c2 j l y) (fun j l ↦ S j l y) (U y)
    ‖iteratedFDeriv ℝ n (fun y ↦ transportRemainder (fun j ↦ A j y)
      (fun j ↦ fderiv ℝ b y (v j)) (B y) (b y)) x‖ ≤
      completeRemainderProfileConstant M (fun j ↦ ‖v j‖) n * H := by
  intro b
  apply (norm_iteratedFDeriv_completeTransportRemainder_le n hA hB hc1 hdU hc2 hS hU x v).trans
  exact (completeTransportDerivativeBound_profile_le hH hM (fun _ ↦ norm_nonneg _) W δ n
    (fun j k hk ↦ ⟨norm_nonneg _, hAP j k hk⟩)
    (fun k hk ↦ ⟨norm_nonneg _, hBP k hk⟩)
    (fun j k hk ↦ ⟨norm_nonneg _, hc1P j k hk⟩)
    (fun j k hk ↦ ⟨norm_nonneg _, hdUP j k hk⟩)
    (fun j l k hk ↦ ⟨norm_nonneg _, hc2P j l k hk⟩)
    (fun j l k hk ↦ ⟨norm_nonneg _, hSP j l k hk⟩)
    (fun k hk ↦ ⟨norm_nonneg _, hUP k hk⟩)).trans
    (transportProfile_le_oneHigh hH
      (completeRemainderProfileConstant_nonneg hM (fun _ ↦ norm_nonneg _) n) hbudget)

end JanetCartan.FourierIntegral
