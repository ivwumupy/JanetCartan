module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.ProfileEstimates

/-!
# Masked transport bounds with a single high norm

For `app:ch_regular_base:eq:actual-global-cutoff` and
`app:ch_regular_base:eq:actual-one-high`, all three masks are differentiated before
collapsing the common interpolation exponent. The concrete results below require
only profiles of the original primitives, never a correction or remainder bound.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.FourierIntegral

/-- Constant for the three masks in `app:ch_regular_base:eq:actual-global-cutoff`.
It depends on the fixed primitive constants, not on the high coefficient norm. -/
def maskedTransportProfileConstant (M C : ℕ → ℝ) : ℕ → ℝ :=
  transportLeibnizBound M (transportLeibnizBound M (transportLeibnizBound M C))

/-- Positivity needed for the final one-high collapse in
`app:ch_regular_base:eq:actual-one-high`. -/
theorem maskedTransportProfileConstant_nonneg {M C : ℕ → ℝ}
    (hM : ∀ k, 0 ≤ M k) (hC : ∀ k, 0 ≤ C k) (n : ℕ) :
    0 ≤ maskedTransportProfileConstant M C n :=
  transportLeibnizBound_nonneg hM
    (transportLeibnizBound_nonneg hM (transportLeibnizBound_nonneg hM hC)) n

variable {E R ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℂ R] [Fintype ι]
local instance : NormedAlgebra ℝ R := NormedAlgebra.restrictScalars ℝ ℂ R

/-- Assembly of a previously proved amplitude profile with three primitive mask
profiles. The concrete amplitude theorems below discharge `hbP` from the actual
transport formulas (`app:ch_regular_base:eq:actual-one-high`). -/
theorem norm_iteratedFDeriv_maskedTransportAmplitude_oneHigh (n W δ d : ℕ)
    {χt χs χg : E → ℂ} {b : E → R}
    (ht : ContDiff ℝ n χt) (hs : ContDiff ℝ n χs)
    (hg : ContDiff ℝ n χg) (hb : ContDiff ℝ n b)
    {M C : ℕ → ℝ} (hM : ∀ k, 0 ≤ M k) (hC : ∀ k, 0 ≤ C k)
    {H : ℝ} (hH : 1 ≤ H) (x : E) (hbudget : n + (3 * δ + d) ≤ W)
    (htP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k χt x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hsP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k χs x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hgP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k χg x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hbP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k b x‖ ≤ C k * H ^ (((k + d : ℕ) : ℝ) / W)) :
    ‖iteratedFDeriv ℝ n (fun y ↦ maskedTransportAmplitude
      (χt y) (χs y) (χg y) (b y)) x‖ ≤ maskedTransportProfileConstant M C n * H := by
  apply (norm_iteratedFDeriv_maskedTransportAmplitude_le ht hs hg hb x n le_rfl).trans
  exact (maskedTransportDerivativeBound_profile_le (lt_of_lt_of_le zero_lt_one hH)
    hM hC W δ d n (fun k hk ↦ ⟨norm_nonneg _, htP k hk⟩)
    (fun k hk ↦ ⟨norm_nonneg _, hsP k hk⟩)
    (fun k hk ↦ ⟨norm_nonneg _, hgP k hk⟩) hbP).trans
    (transportProfile_le_oneHigh hH (maskedTransportProfileConstant_nonneg hM hC n) hbudget)

/-- The literal masked leadingAmplitude has one high coefficient factor,
including every source, target and angle mask derivative. Source:
`app:ch_regular_base:eq:actual-one-high` and `app:ch_regular_base:eq:actual-global-cutoff`. -/
theorem norm_iteratedFDeriv_masked_leadingAmplitude_oneHigh (n W δ : ℕ)
    {c U : E → R} (hc : ContDiff ℝ n c) (hU : ContDiff ℝ n U)
    {χt χs χg : E → ℂ}
    (ht : ContDiff ℝ n χt) (hs : ContDiff ℝ n χs) (hg : ContDiff ℝ n χg)
    {M : ℕ → ℝ} (hM : ∀ k, 0 ≤ M k) {H : ℝ} (hH : 1 ≤ H) (x : E)
    (htP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k χt x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hsP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k χs x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hgP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k χg x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hbudget : n + (3 * δ + (δ + δ)) ≤ W)
    (hcP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k c x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hUP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k U x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W)) :
    ‖iteratedFDeriv ℝ n (fun y ↦ maskedTransportAmplitude (χt y) (χs y) (χg y) (leadingAmplitude (c y) (U y))) x‖ ≤
      maskedTransportProfileConstant M (transportLeibnizBound M M) n * H := by
  apply norm_iteratedFDeriv_maskedTransportAmplitude_oneHigh n W δ (δ + δ) ht hs hg
    (hc.mul hU) hM (transportLeibnizBound_nonneg hM hM) hH x hbudget htP hsP hgP
  intro k hk
  have hkn : (k : ℕ∞ω) ≤ n := by exact_mod_cast hk
  exact norm_iteratedFDeriv_leadingAmplitude_profile k W δ
      (hc.of_le hkn) (hU.of_le hkn) hM hH x (fun q hq ↦ hcP q (hq.trans hk)) (fun q hq ↦ hUP q (hq.trans hk))

/-- The literal masked correctionAmplitude has one high coefficient factor,
including every source, target and angle mask derivative. Source:
`app:ch_regular_base:eq:actual-one-high` and `app:ch_regular_base:eq:actual-global-cutoff`. -/
theorem norm_iteratedFDeriv_masked_correctionAmplitude_oneHigh (n W δ : ℕ)
    {c1 dU : ι → E → R} {c2 : ι → ι → E → R}
    {S : ι → ι → E → ℂ} {U : E → R}
    (hc1 : ∀ j, ContDiff ℝ n (c1 j)) (hdU : ∀ j, ContDiff ℝ n (dU j))
    (hc2 : ∀ j l, ContDiff ℝ n (c2 j l))
    (hS : ∀ j l, ContDiff ℝ n (S j l)) (hU : ContDiff ℝ n U)
    {χt χs χg : E → ℂ}
    (ht : ContDiff ℝ n χt) (hs : ContDiff ℝ n χs) (hg : ContDiff ℝ n χg)
    {M : ℕ → ℝ} (hM : ∀ k, 0 ≤ M k) {H : ℝ} (hH : 1 ≤ H) (x : E)
    (htP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k χt x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hsP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k χs x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hgP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k χg x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hbudget : n + (3 * δ + (3 * δ)) ≤ W)
    (hc1P : ∀ j k, k ≤ n → ‖iteratedFDeriv ℝ k (c1 j) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hdUP : ∀ j k, k ≤ n → ‖iteratedFDeriv ℝ k (dU j) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hc2P : ∀ j l k, k ≤ n → ‖iteratedFDeriv ℝ k (c2 j l) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hSP : ∀ j l k, k ≤ n → ‖iteratedFDeriv ℝ k (S j l) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hUP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k U x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W)) :
    ‖iteratedFDeriv ℝ n (fun y ↦ maskedTransportAmplitude (χt y) (χs y) (χg y) (correctionAmplitude (fun j ↦ c1 j y)
      (fun j ↦ dU j y) (fun j l ↦ c2 j l y) (fun j l ↦ S j l y) (U y))) x‖ ≤
      maskedTransportProfileConstant M (correctionProfileConstant (ι := ι) M) n * H := by
  apply norm_iteratedFDeriv_maskedTransportAmplitude_oneHigh n W δ (3 * δ) ht hs hg
    (contDiff_correctionAmplitude hc1 hdU hc2 hS hU) hM (correctionProfileConstant_nonneg hM) hH x hbudget htP hsP hgP
  intro k hk
  have hkn : (k : ℕ∞ω) ≤ n := by exact_mod_cast hk
  exact norm_iteratedFDeriv_correctionAmplitude_profile k W δ
      (fun j ↦ (hc1 j).of_le hkn) (fun j ↦ (hdU j).of_le hkn)
      (fun j l ↦ (hc2 j l).of_le hkn) (fun j l ↦ (hS j l).of_le hkn) (hU.of_le hkn)
      hM hH x (fun j q hq ↦ hc1P j q (hq.trans hk))
      (fun j q hq ↦ hdUP j q (hq.trans hk)) (fun j l q hq ↦ hc2P j l q (hq.trans hk))
      (fun j l q hq ↦ hSP j l q (hq.trans hk)) (fun q hq ↦ hUP q (hq.trans hk))

/-- The literal masked completeTransportRemainder has one high coefficient factor,
including every source, target and angle mask derivative. Source:
`app:ch_regular_base:eq:actual-one-high` and `app:ch_regular_base:eq:actual-global-cutoff`. -/
theorem norm_iteratedFDeriv_masked_completeTransportRemainder_oneHigh (n W δ : ℕ)
    {A : ι → E → R} {B : E → R}
    {c1 dU : ι → E → R} {c2 : ι → ι → E → R}
    {S : ι → ι → E → ℂ} {U : E → R}
    (hA : ∀ j, ContDiff ℝ n (A j)) (hB : ContDiff ℝ n B)
    (hc1 : ∀ j, ContDiff ℝ (n + 1) (c1 j)) (hdU : ∀ j, ContDiff ℝ (n + 1) (dU j))
    (hc2 : ∀ j l, ContDiff ℝ (n + 1) (c2 j l))
    (hS : ∀ j l, ContDiff ℝ (n + 1) (S j l)) (hU : ContDiff ℝ (n + 1) U)
    {χt χs χg : E → ℂ}
    (ht : ContDiff ℝ n χt) (hs : ContDiff ℝ n χs) (hg : ContDiff ℝ n χg)
    {M : ℕ → ℝ} (hM : ∀ k, 0 ≤ M k) {H : ℝ} (hH : 1 ≤ H) (x : E) (v : ι → E)
    (htP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k χt x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hsP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k χs x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hgP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k χg x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hbudget : n + (3 * δ + (4 * δ + 1)) ≤ W)
    (hAP : ∀ j k, k ≤ n → ‖iteratedFDeriv ℝ k (A j) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hBP : ∀ k ≤ n, ‖iteratedFDeriv ℝ k B x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hc1P : ∀ j k, k ≤ n + 1 → ‖iteratedFDeriv ℝ k (c1 j) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hdUP : ∀ j k, k ≤ n + 1 → ‖iteratedFDeriv ℝ k (dU j) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hc2P : ∀ j l k, k ≤ n + 1 → ‖iteratedFDeriv ℝ k (c2 j l) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hSP : ∀ j l k, k ≤ n + 1 → ‖iteratedFDeriv ℝ k (S j l) x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hUP : ∀ k ≤ n + 1, ‖iteratedFDeriv ℝ k U x‖ ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W)) :
    let b := fun y ↦ correctionAmplitude (fun j ↦ c1 j y) (fun j ↦ dU j y)
      (fun j l ↦ c2 j l y) (fun j l ↦ S j l y) (U y)
    ‖iteratedFDeriv ℝ n (fun y ↦ maskedTransportAmplitude (χt y) (χs y) (χg y) (transportRemainder (fun j ↦ A j y)
      (fun j ↦ fderiv ℝ b y (v j)) (B y) (b y))) x‖ ≤
      maskedTransportProfileConstant M (completeRemainderProfileConstant M (fun j ↦ ‖v j‖)) n * H := by
  intro b
  apply norm_iteratedFDeriv_maskedTransportAmplitude_oneHigh n W δ (4 * δ + 1) ht hs hg
    (contDiff_completeTransportRemainder n v hA hB
      (contDiff_correctionAmplitude hc1 hdU hc2 hS hU)) hM (completeRemainderProfileConstant_nonneg hM (fun _ ↦ norm_nonneg _)) hH x hbudget htP hsP hgP
  intro k hk
  have hkn : (k : ℕ∞ω) ≤ n := by exact_mod_cast hk
  have hk1 : (k + 1 : ℕ∞ω) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.add_le_add_right hk 1
  exact norm_iteratedFDeriv_completeTransportRemainder_profile k W δ
      (fun j ↦ (hA j).of_le hkn) (hB.of_le hkn)
      (fun j ↦ (hc1 j).of_le hk1) (fun j ↦ (hdU j).of_le hk1)
      (fun j l ↦ (hc2 j l).of_le hk1) (fun j l ↦ (hS j l).of_le hk1) (hU.of_le hk1)
      hM hH x v (fun j q hq ↦ hAP j q (hq.trans hk)) (fun q hq ↦ hBP q (hq.trans hk))
      (fun j q hq ↦ hc1P j q (by omega)) (fun j q hq ↦ hdUP j q (by omega))
      (fun j l q hq ↦ hc2P j l q (by omega)) (fun j l q hq ↦ hSP j l q (by omega))
      (fun q hq ↦ hUP q (by omega))

end JanetCartan.FourierIntegral
