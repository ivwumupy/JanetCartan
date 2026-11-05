module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeightedBranches
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FirstOutputBounds

/-!
# The fixed extra derivative in the gain-one primitive budget

Numerical profiles for the gain-one paragraph after
`app:ch_regular_base:eq:graph-derivative-transfer`. The consumer is the actual
first-output branch estimate, with low reserve `μ₀`, baseline `μ₀ + 1`, and
remaining Sobolev order `s - 1`. The normalized-profile producer must establish
the individual primitive bounds; no first-output bound is an input.
-/

@[expose] public noncomputable section
namespace JanetCartan.FourierIntegral.GainOneBranches

/-- Individual primitive interpolation profile. The extra initial derivative
is absorbed by choosing `μ = μ₀ + 1`, once, in the gain-one paragraph following
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
def profile (μ t : ℕ) (H : ℝ) (j : ℕ) : ℝ :=
  H ^ (((j - μ : ℕ) : ℝ) / t)

/-- Nonnegativity of the primitive profile (gain one, `app:ch_regular_base:thm:actual-calculus`, Step 3). -/
theorem profile_nonneg (μ t j : ℕ) {H : ℝ} (hH : 1 ≤ H) :
    0 ≤ profile μ t H j := Real.rpow_nonneg (zero_le_one.trans hH) _

/-- A primitive profile increases with the derivative order (gain one, `app:ch_regular_base:thm:actual-calculus`, Step 3). -/
theorem profile_mono (μ t : ℕ) {H : ℝ} (hH : 1 ≤ H) :
    Monotone (profile μ t H) := by
  intro a b hab
  apply Real.rpow_le_rpow_of_exponent_le hH
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg t)
  exact_mod_cast Nat.sub_le_sub_right hab μ

/-- Multiplying primitive profiles spends one shared excess budget, rather
than one high bound per factor. Source: `app:ch_regular_base:thm:actual-calculus`, gain-one paragraph. -/
theorem profile_mul_le (μ t a b : ℕ) {H : ℝ} (hH : 1 ≤ H) :
    profile μ t H a * profile μ t H b ≤ profile μ t H (a + b) := by
  unfold profile
  rw [← Real.rpow_add (by linarith : 0 < H), ← add_div]
  apply Real.rpow_le_rpow_of_exponent_le hH
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg t)
  exact_mod_cast (show a - μ + (b - μ) ≤ a + b - μ by omega)

/-- The endpoint/interpolation inputs used for order zero also supply each
individual gain-one profile at the enlarged baseline. Producer:
`jc-fio-sobolev-normalized-profiles`; consumer: the branch bounds below.
Source: the interpolation paragraph preceding `app:ch_regular_base:eq:fio-input`. -/
theorem profile_of_interpolation (q : ℕ → ℝ) (μ t j : ℕ) (L K H : ℝ)
    (hq : ∀ a, 0 ≤ q a) (hmono : Monotone q)
    (hL : 1 ≤ L) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : q μ ≤ L) (hhigh : q (μ + t) ≤ H) (hj : j ≤ μ + t)
    (hinterp : μ < j → j < μ + t →
      q j ≤ K * q μ ^ (1 - ((j - μ : ℕ) : ℝ) / t) *
        q (μ + t) ^ (((j - μ : ℕ) : ℝ) / t)) :
    q j ≤ (K * L) * profile μ t H j :=
  JointBudget.interpolation_le_scaled_rpow q μ t j L K H hq hmono
    hL hK hH hlow hhigh hj hinterp

end JanetCartan.FourierIntegral.GainOneBranches
