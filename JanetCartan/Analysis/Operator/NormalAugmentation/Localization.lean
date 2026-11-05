module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Localization estimates for exterior completion

The norm inequalities in Step 4 of `app:ch_background:prop:bg-frame`.
The cutoff is a bounded linear operator; no idempotence is required. For the
paper it is multiplication by `ψ`, and its complement is multiplication by `1-ψ`.
The analytic local gap and the support property of the cutoff are explicit inputs.
-/

@[expose] public noncomputable section

namespace JanetCartan.NormalAugmentation

variable {H P Z : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The exterior cutoff `1-ψ` in `app:ch_background:defn:bg-row`. -/
def exterior (χ : H →L[ℝ] H) : H →L[ℝ] H := 1 - χ

/-- The exact cutoff partition used in `app:ch_background:prop:bg-frame`, Step 4. -/
theorem cutoff_add_exterior (χ : H →L[ℝ] H) (f : H) :
    χ f + exterior χ f = f := by
  simp [exterior]

/-- On the plateau of `ψ`, the exterior channel vanishes
(`app:ch_background:prop:bg-frame`). -/
theorem exterior_eq_zero_of_cutoff_eq (χ : H →L[ℝ] H) {f : H} (hf : χ f = f) :
    exterior χ f = 0 := by
  simp [exterior, hf]

/-- The exterior channel has zero restriction to the core whenever `ψ = 1`
there (`app:ch_background:prop:bg-frame`). The map `J` can be restriction to
the core; only the literal plateau identity is used. -/
theorem restriction_comp_exterior_eq_zero
    (χ : H →L[ℝ] H) (J : H →L[ℝ] Z) (hplateau : J.comp χ = J) :
    J.comp (exterior χ) = 0 := by
  ext f
  have h := congrArg (fun T : H →L[ℝ] Z ↦ T f) hplateau
  simpa [exterior, map_sub] using sub_eq_zero.mpr h.symm

/-- The localization error is bounded by the exterior observation, using only global
row boundedness (`app:ch_background:prop:bg-frame`, Step 4). -/
theorem norm_localization_error_le (B : H →L[ℝ] P) (χ : H →L[ℝ] H) (f : H) :
    ‖B (χ f) - B f‖ ≤ ‖B‖ * ‖exterior χ f‖ := by
  have h : B (χ f) - B f = -B (exterior χ f) := by
    simp [exterior, map_sub]
  rw [h, norm_neg]
  exact B.le_opNorm _

/-- The intermediate observation inequality in `app:ch_background:prop:bg-frame`. -/
theorem norm_localized_observation_le (B : H →L[ℝ] P) (χ : H →L[ℝ] H) (f : H) :
    ‖B (χ f)‖ ≤ ‖B f‖ + ‖B‖ * ‖exterior χ f‖ := by
  calc
    ‖B (χ f)‖ ≤ ‖B f‖ + ‖B (χ f) - B f‖ := norm_le_insert' _ _
    _ ≤ ‖B f‖ + ‖B‖ * ‖exterior χ f‖ :=
      add_le_add le_rfl (norm_localization_error_le B χ f)

/-- The unsquared exterior-completion estimate in
`app:ch_background:prop:bg-frame`, with explicit constants. -/
theorem norm_le_of_localized_estimate (B : H →L[ℝ] P) (χ : H →L[ℝ] H)
    {K : ℝ} (hK : 0 ≤ K) (hlocal : ∀ f, ‖χ f‖ ≤ K * ‖B (χ f)‖) (f : H) :
    ‖f‖ ≤ K * ‖B f‖ + (1 + K * ‖B‖) * ‖exterior χ f‖ := by
  calc
    ‖f‖ ≤ ‖χ f‖ + ‖exterior χ f‖ := by
      nth_rw 1 [← cutoff_add_exterior χ f]
      exact norm_add_le _ _
    _ ≤ K * ‖B (χ f)‖ + ‖exterior χ f‖ := add_le_add (hlocal f) le_rfl
    _ ≤ K * (‖B f‖ + ‖B‖ * ‖exterior χ f‖) + ‖exterior χ f‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_localized_observation_le B χ f) hK) le_rfl
    _ = K * ‖B f‖ + (1 + K * ‖B‖) * ‖exterior χ f‖ := by ring

/-- Squaring the two-observation estimate in `app:ch_background:prop:bg-frame`
by the two-dimensional Cauchy inequality. -/
theorem norm_sq_le_of_localized_estimate (B : H →L[ℝ] P) (χ : H →L[ℝ] H)
    {K : ℝ} (hK : 0 ≤ K) (hlocal : ∀ f, ‖χ f‖ ≤ K * ‖B (χ f)‖) (f : H) :
    ‖f‖ ^ 2 ≤ (K ^ 2 + (1 + K * ‖B‖) ^ 2) *
      (‖B f‖ ^ 2 + ‖exterior χ f‖ ^ 2) := by
  have h := norm_le_of_localized_estimate B χ hK hlocal f
  have hs : ‖f‖ ^ 2 ≤ (K * ‖B f‖ + (1 + K * ‖B‖) * ‖exterior χ f‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (K * ‖exterior χ f‖ - (1 + K * ‖B‖) * ‖B f‖)]

/-- Conversion of the squared local gap `app:ch_background:eq:bg-local-bound`
to the norm estimate used in exterior completion. -/
theorem norm_le_of_local_gap (B : H →L[ℝ] P) {c : ℝ} (hc : 0 < c) {g : H}
    (hgap : c * ‖g‖ ^ 2 ≤ ‖B g‖ ^ 2) :
    ‖g‖ ≤ (Real.sqrt c)⁻¹ * ‖B g‖ := by
  have hs : Real.sqrt c * ‖g‖ ≤ ‖B g‖ := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    simpa only [mul_pow, Real.sq_sqrt hc.le] using hgap
  have h := (le_div_iff₀ (Real.sqrt_pos.2 hc)).mpr (by simpa [mul_comm] using hs)
  simpa [div_eq_mul_inv, mul_comm] using h

/-- Absorb a controlled remainder into the local gap, as in Step 3 of
`app:ch_background:prop:bg-frame`. The analytic frozen-symbol and small-support
estimates supplying the two premises are not asserted here. -/
theorem local_gap_of_remainder_bound (B : H →L[ℝ] P) (R : H →L[ℝ] Z)
    (S : Submodule ℝ H) {c ε : ℝ}
    (hcore : ∀ g ∈ S, c * ‖g‖ ^ 2 ≤ ‖B g‖ ^ 2 + ‖R g‖ * ‖g‖)
    (herror : ∀ g ∈ S, ‖R g‖ ≤ ε * ‖g‖) {g : H} (hg : g ∈ S) :
    (c - ε) * ‖g‖ ^ 2 ≤ ‖B g‖ ^ 2 := by
  have h := mul_le_mul_of_nonneg_right (herror g hg) (norm_nonneg g)
  nlinarith [hcore g hg]

end JanetCartan.NormalAugmentation
