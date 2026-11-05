module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Approximation.Integral
public import JanetCartan.Analysis.Approximation.BallSmoothing.Cutoff.Basic

/-!
# Approximation by the actual finite-moment inward smoother

This proves `app:ch_regular_base:eq:ball-extension-continuous` for the literal
operator in `paper-v2.tex`. The fixed normalized kernel, finite binomial
coefficients, and actual thin physical cutoff are all instantiated. Smoothness
up to the boundary means smoothness at each point of the closed unit ball,
and all derivatives in the estimate are the original ambient derivatives
restricted to that ball. The constant is fixed before the scale and input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff

namespace JanetCartan.BallSmoothing

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Pointwise approximation on the full closed unit ball by the SAME
finite-moment inward smoother. The actual cutoff is one there, so the
remainder is precisely the proved averaged Taylor remainder
(`app:ch_regular_base:eq:ball-extension-continuous`). -/
theorem norm_radialSmoothing_sub_le
    {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : (2 : ℝ) * m ≤ R)
    (f : E → F) (hf : ∀ z ∈ closedBall (0 : E) 1, ContDiffAt ℝ ∞ f z)
    {x : E} (hx : x ∈ closedBall 0 1) :
    ‖radialSmoothing (unitCutoff n R) (coefficient m) (kernel n) R m f x - f x‖ ≤
      radialApproximationConstant m * (R⁻¹)^m * cNorm (closedBall 0 1) m f := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hR1 : 1 ≤ R := by linarith
  simpa only [radialSmoothing, unitCutoff_eq_one n hR1 hx, one_smul] using
    norm_radialCombination_sub_le hm hR f hf hx

/-- The exact native closed-ball `C⁰` approximation estimate uses `m`
original input derivatives and the explicit constant depending only on `m`.
It applies componentwise in every real Banach target, including the vector
and tensor fields of `main:lem:smoothing`
(`app:ch_regular_base:eq:ball-extension-continuous`). -/
theorem cNorm_radialSmoothing_sub_le
    {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : (2 : ℝ) * m ≤ R)
    (f : E → F) (hf : ∀ z ∈ closedBall (0 : E) 1, ContDiffAt ℝ ∞ f z) :
    cNorm (closedBall (0 : E) 1) 0
        (radialSmoothing (unitCutoff n R) (coefficient m) (kernel n) R m f - f) ≤
      radialApproximationConstant m * (R⁻¹)^m * cNorm (closedBall 0 1) m f := by
  rw [cNorm_order_zero]
  apply Real.sSup_le
  · rintro _ ⟨x, hx, rfl⟩
    exact norm_radialSmoothing_sub_le hm hR f hf hx
  · have hR0 : 0 ≤ R := (by positivity : (0 : ℝ) ≤ 2 * m).trans hR
    exact mul_nonneg
      (mul_nonneg (radialApproximationConstant_nonneg m) (pow_nonneg (inv_nonneg.mpr hR0) m))
      (cNorm_nonneg _ _ _)

/-- Choose the approximation constant before `R` and the original input.
The operator is the fixed literal construction from
`app:ch_regular_base:eq:extension-radial-formula`; the same explicit constant
works for every target Banach space. This is the approximation clause consumed
by the ball-smoothing assembly in
`app:ch_regular_base:lem:ball-extension`. -/
theorem exists_radialSmoothing_approximation_constant (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, (2 : ℝ) * m ≤ R →
      ∀ f : E → F, (∀ z ∈ closedBall (0 : E) 1, ContDiffAt ℝ ∞ f z) →
        cNorm (closedBall (0 : E) 1) 0
            (radialSmoothing (unitCutoff n R) (coefficient m) (kernel n) R m f - f) ≤
          C * (R⁻¹)^m * cNorm (closedBall 0 1) m f :=
  ⟨radialApproximationConstant m, radialApproximationConstant_nonneg m,
    fun _ hR f hf ↦ cNorm_radialSmoothing_sub_le hm hR f hf⟩

end JanetCartan.BallSmoothing
