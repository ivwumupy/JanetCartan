module
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteAmplitudeSplit
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteSourceProfiles
public import JanetCartan.Iteration.PhysicalPairs.ColoredWindow
/-! # Exact whole-chart single-node amplitude profile join

The inputs are precisely baseline112's native outer profile and source15's
whole-native finite-source profile. This deduction retains A=B+D before any
product estimate. The genuine R-profile is proved first; only afterward is it
allowed to enter the already fixed larger pair fine envelope. This lemma alone
does not instantiate the actual full-forcing Picard profile or baseline112
(`main:eq:mean-final-amplitude`, `main:prop:pairs`).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeProfiles
/-- Combine the exact complete B+D germ with the genuine coefficient/native
source jets, with no physical-lambda or Fourier-envelope substitute. -/
theorem complete_true_R_profile {n N : ℕ} {U : Set (Euclidean n)} (hU : IsOpen U)
    (A B D : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (heq : ∀ x ∈ U, A x = B x+D x)
    (hB : ContDiffOn ℝ ∞ B U) (hD : ContDiffOn ℝ ∞ D U)
    (CB CD : ℕ → ℝ) (hCB : ∀ j, 0 ≤ CB j) (hCD : ∀ j, 0 ≤ CD j)
    {T R h : ℝ} (hT : 0 ≤ T) (hTR : T ≤ R) (hR : 1 ≤ R) (hh : h ≤ 1)
    (hBj : ∀ j x, x ∈ U → ‖iteratedFDeriv ℝ j B x‖ ≤ CB j*T^j)
    (hDj : ∀ j x, x ∈ U → ‖iteratedFDeriv ℝ j D x‖ ≤ CD j*h*R^j) :
    ContDiffOn ℝ ∞ A U ∧
      ∀ j x, x ∈ U → ‖iteratedFDeriv ℝ j A x‖ ≤ (CB j+CD j)*R^j := by
  refine ⟨(hB.add hD).congr heq, ?_⟩
  intro j x hx
  have hmem : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hx
  have hg : A =ᶠ[𝓝 x] (B+D) := hmem.mono (fun y hy ↦ heq y hy)
  have hb : ContDiffAt ℝ j B x := ((hB x hx).contDiffAt (hU.mem_nhds hx)).of_le (by simp)
  have hd : ContDiffAt ℝ j D x := ((hD x hx).contDiffAt (hU.mem_nhds hx)).of_le (by simp)
  rw [(hg.iteratedFDeriv ℝ j).eq_of_nhds,iteratedFDeriv_add_apply hb hd]
  have bp := (hBj j x hx).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT hTR j) (hCB j))
  have dp := (hDj j x hx).trans (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (hCD j) hh) (pow_nonneg (zero_le_one.trans hR) j))
  exact ((norm_add_le _ _).trans (add_le_add bp dp)).trans_eq (by ring)

/-- Only after proving true R-jets, use the SAME original fine envelope to feed
its first-mask ledger. This does not reverse the implication. -/
theorem R_le_original_fine (C : ℝ) {R : ℝ} (hR : 1 ≤ R) :
    R ≤ OriginalWindow.fineScale C R := by
  calc
    R = R^(1 : ℝ) := (Real.rpow_one R).symm
    _ ≤ R^(1+meanSlack) := Real.rpow_le_rpow_of_exponent_le hR (by norm_num [meanSlack])
    _ = 1*R^(1+meanSlack) := (one_mul _).symm
    _ ≤ OriginalWindow.fineScale C R := mul_le_mul_of_nonneg_right (le_max_left 1 C)
      (Real.rpow_nonneg (zero_le_one.trans hR) _)
/-- Admission to the existing pair ledger uses true R jets only in the safe
larger-envelope direction; the source estimate is never inferred backwards. -/
theorem jet_le_original_fine {n N : ℕ}
    (A : Euclidean n → Matrix (Fin N) (Fin n) ℂ) (Cscale C R : ℝ)
    (hC : 0 ≤ C) (hR : 1 ≤ R) (j : ℕ) (x : Euclidean n)
    (hjet : ‖iteratedFDeriv ℝ j A x‖ ≤ C*R^j) :
    ‖iteratedFDeriv ℝ j A x‖ ≤ C*(OriginalWindow.fineScale Cscale R)^j :=
  hjet.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (zero_le_one.trans hR) (R_le_original_fine Cscale hR) j) hC)
end JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeProfiles
