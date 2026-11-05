module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.PhaseJets

/-!
# Joint jet estimates used by the exact WKB polynomial

The bilinear Leibniz convolution preserves the positive-part baseline. These
local estimates feed the four geometric coefficients in
`app:ch_waves:eq:exact-W-amplitude` and the differentiated polynomial in
`app:ch_waves:eq:WKB-amplitude-difference`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace JanetCartan.RawPrimary.AmplitudeGrades.Polynomial

variable {X E F G : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Fixed Leibniz constants for the tensor coefficients of
`app:ch_waves:eq:WKB-amplitude-difference`. -/
def productProfile (B : E →L[ℝ] F →L[ℝ] G) (A C : ℕ → ℝ) (j : ℕ) : ℝ :=
  ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A i * C (j - i)

/-- Nonnegativity of the fixed tensor constants
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem productProfile_nonneg (B : E →L[ℝ] F →L[ℝ] G)
    {A C : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) (hC : ∀ j, 0 ≤ C j) (j : ℕ) :
    0 ≤ productProfile B A C j := by
  unfold productProfile
  exact mul_nonneg (norm_nonneg B) (Finset.sum_nonneg fun i _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA _)) (hC _))

/-- Addition of joint jets in the exact WKB polynomial, locally on its
original domain (`app:ch_waves:eq:exact-W-amplitude`). -/
theorem jet_add_le {f g : X → E} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ f y + g y) x‖ ≤
      ‖iteratedFDeriv ℝ j f x‖ + ‖iteratedFDeriv ℝ j g x‖ := by
  change ‖iteratedFDeriv ℝ j (f + g) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hf.of_le (by simp)) (hg.of_le (by simp))]
  exact norm_add_le _ _

/-- Constant complex multiplication retains its exact size in every joint
jet (`app:ch_waves:eq:exact-W-amplitude`). -/
theorem jet_const_smul [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    {f : X → E} {x : X} (hf : ContDiffAt ℝ ∞ f x) (a : ℂ) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ a • f y) x‖ =
      ‖a‖ * ‖iteratedFDeriv ℝ j f x‖ := by
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (by simp)), norm_smul]

/-- The truncated baseline survives all Leibniz splittings. This is the
joint, rather than pointwise, product step in
`app:ch_waves:eq:WKB-amplitude-difference`. -/
theorem jet_bilinear_le (B : E →L[ℝ] F →L[ℝ] G)
    {Ω : Set X} (hΩ : IsOpen Ω) {f : X → E} {g : X → F}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    {x : X} (hx : x ∈ Ω) {b : ℕ} {L : ℝ} (hL : 1 ≤ L)
    {A C : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) (hC : ∀ j, 0 ≤ C j)
    (hfj : ∀ j, ‖iteratedFDeriv ℝ j f x‖ ≤ A j * L ^ (j - b))
    (hgj : ∀ j, ‖iteratedFDeriv ℝ j g x‖ ≤ C j * L ^ (j - b)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ B (f y) (g y)) x‖ ≤
      productProfile B A C j * L ^ (j - b) := by
  have hh := B.norm_iteratedFDerivWithin_le_of_bilinear hf hg hΩ.uniqueDiffOn hx
    (by simp : (j : ℕ∞ω) ≤ ∞)
  simp only [iteratedFDerivWithin_of_isOpen _ hΩ hx] at hh
  apply hh.trans
  unfold productProfile
  rw [mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  calc
    (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖ ≤
        (j.choose i : ℝ) * (A i * L ^ (i - b)) * (C (j - i) * L ^ (j - i - b)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hfj i) (Nat.cast_nonneg _)) (hgj _)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA _)
          (pow_nonneg (le_trans zero_le_one hL) _)))
    _ = ((j.choose i : ℝ) * A i * C (j - i)) * L ^ ((i - b) + (j - i - b)) := by
      rw [pow_add]; ring
    _ ≤ ((j.choose i : ℝ) * A i * C (j - i)) * L ^ (j - b) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega))
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA _)) (hC _))

/-- Lowering only the retained baseline, without changing the fixed
constant, for the polynomial's different coefficient orders
(`app:ch_waves:thm:wkb`). -/
theorem jet_lower_baseline {f : X → E} {x : X} {b c : ℕ} {L : ℝ}
    {A : ℕ → ℝ} (hL : 1 ≤ L) (hA : ∀ j, 0 ≤ A j) (hbc : b ≤ c)
    (hf : ∀ j, ‖iteratedFDeriv ℝ j f x‖ ≤ A j * L ^ (j - c)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ A j * L ^ (j - b) :=
  (hf j).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (by omega)) (hA j))

/-- From a total-joint profile to every physical/parameter splitting with
`k ≤ rpar`; the resulting multilinear norm also controls all unit-direction
mixed derivatives (`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem jet_mixed_order_le {f : X → E} {x : X} {rpar r k : ℕ}
    {L a : ℝ} {C : ℕ → ℝ} (hL : 1 ≤ L) (ha : 0 ≤ a)
    (hC : ∀ j, 0 ≤ C j) (hk : k ≤ rpar)
    (hf : ∀ j, ‖iteratedFDeriv ℝ j f x‖ ≤ a * C j * L ^ (j - rpar)) :
    ‖iteratedFDeriv ℝ (r + k) f x‖ ≤ a * C (r + k) * L ^ r :=
  (hf _).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (by omega)) (mul_nonneg ha (hC _)))

/-- Summing joint jet bounds yields the project's actual `cNorm` profile;
this is used for the polynomial output of `app:ch_waves:thm:wkb`. -/
theorem profile_of_jet_bounds {J : Set X} {f : X → E} {b : ℕ}
    {L a : ℝ} {C : ℕ → ℝ} (hL : 1 ≤ L) (ha : 0 ≤ a)
    (hC : ∀ j, 0 ≤ C j)
    (hf : ∀ j, ∀ x ∈ J, ‖iteratedFDeriv ℝ j f x‖ ≤ a * C j * L ^ (j - b)) :
    HasDerivativeProfile J f b L
      (fun j ↦ a * ∑ i ∈ Finset.range (j + 1), C i) := by
  intro j
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  apply (cNorm_le_sum_of_bounds (fun i _ ↦ mul_nonneg (mul_nonneg ha (hC i)) (pow_nonneg hL0 _))
    (fun i _ x hx ↦ hf i x hx)).trans
  dsimp only
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (by have := Finset.mem_range.mp hi; omega))
    (mul_nonneg ha (hC _))

end JanetCartan.RawPrimary.AmplitudeGrades.Polynomial
