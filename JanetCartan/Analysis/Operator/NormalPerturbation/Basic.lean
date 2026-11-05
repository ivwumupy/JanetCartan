module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Perturbing a row and its output normal

The algebra behind `app:ch_waves:eq:colored-normal-comparison` and
`app:ch_response:cor:current-atoms`. Analytic bounds on the perturbation are
inputs; no corrected atomic family is constructed here.
-/

@[expose] public noncomputable section

open scoped InnerProduct
open ContinuousLinearMap

namespace JanetCartan.NormalPerturbation

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The output normal `AA*` of a row, as in
`app:ch_waves:eq:colored-normal-comparison`. -/
def normal (A : E →L[𝕜] F) : F →L[𝕜] F := A ∘L A†

/-- Exact expansion underlying `app:ch_response:cor:current-atoms`. -/
theorem normal_add_sub (A D : E →L[𝕜] F) :
    normal (A + D) - normal A = A ∘L D† + D ∘L A† + normal D := by
  simp only [normal, map_add, comp_add, add_comp]
  abel

/-- The normal has squared row norm
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem norm_normal (A : E →L[𝕜] F) : ‖normal A‖ = ‖A‖ ^ 2 := by
  simpa [normal, pow_two] using norm_adjoint_comp_self (A†)

/-- The sharp elementary perturbation bound used in
`app:ch_response:cor:current-atoms`. -/
theorem norm_normal_add_sub_le (A D : E →L[𝕜] F) :
    ‖normal (A + D) - normal A‖ ≤ 2 * ‖A‖ * ‖D‖ + ‖D‖ ^ 2 := by
  rw [normal_add_sub]
  calc
    ‖A ∘L D† + D ∘L A† + normal D‖ ≤
        ‖A ∘L D†‖ + ‖D ∘L A†‖ + ‖normal D‖ := norm_add₃_le
    _ ≤ ‖A‖ * ‖D†‖ + ‖D‖ * ‖A†‖ + ‖normal D‖ := by
      exact add_le_add (add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)) le_rfl
    _ = 2 * ‖A‖ * ‖D‖ + ‖D‖ ^ 2 := by
      rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, norm_normal]
      ring

/-- Substitute analytic row bounds into the algebraic comparison
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem norm_normal_add_sub_le_of_bounds (A D : E →L[𝕜] F)
    {a d : ℝ} (hA : ‖A‖ ≤ a) (hD : ‖D‖ ≤ d) :
    ‖normal (A + D) - normal A‖ ≤ 2 * a * d + d ^ 2 := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hA
  have hd : 0 ≤ d := (norm_nonneg _).trans hD
  have hmul := mul_le_mul hA hD (norm_nonneg D) ha
  have hsq := mul_self_le_mul_self (norm_nonneg D) hD
  nlinarith [norm_normal_add_sub_le A D]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Row-norm control from the same input bounds
(`app:ch_response:cor:current-atoms`). -/
theorem norm_row_add_le (A D : E →L[𝕜] F)
    {a d : ℝ} (hA : ‖A‖ ≤ a) (hD : ‖D‖ ≤ d) : ‖A + D‖ ≤ a + d :=
  (norm_add_le A D).trans (add_le_add hA hD)

/-- Normal-norm control from row bounds
(`app:ch_response:cor:current-atoms`). -/
theorem norm_normal_add_le (A D : E →L[𝕜] F)
    {a d : ℝ} (hA : ‖A‖ ≤ a) (hD : ‖D‖ ≤ d) :
    ‖normal (A + D)‖ ≤ (a + d) ^ 2 := by
  rw [norm_normal, pow_two, pow_two]
  exact mul_self_le_mul_self (norm_nonneg _) (norm_row_add_le A D hA hD)

omit [CompleteSpace F] in
/-- Operator perturbations transfer a quadratic lower bound on any specified
output class, as stated after `app:ch_waves:eq:colored-normal-comparison`.
The class need not be a subspace and the operators need not be self-adjoint. -/
theorem quadratic_lower_bound_sub_norm (N M : F →L[𝕜] F) (s : Set F) (g : ℝ)
    (hgap : ∀ x ∈ s, g * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (N x) x)) :
    ∀ x ∈ s, (g - ‖M - N‖) * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (M x) x) := by
  intro x hx
  have h := re_inner_le_norm (𝕜 := 𝕜) ((N - M) x) x
  have hop := mul_le_mul_of_nonneg_right ((N - M).le_opNorm x) (norm_nonneg x)
  rw [sub_apply, inner_sub_left, map_sub] at h
  rw [norm_sub_rev N M, sub_apply] at hop
  nlinarith [hgap x hx]

omit [CompleteSpace F] in
/-- Transfer a gap using a supplied normal comparison estimate
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem quadratic_lower_bound_of_norm_sub_le (N M : F →L[𝕜] F)
    (s : Set F) {g ε : ℝ}
    (hgap : ∀ x ∈ s, g * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (N x) x))
    (hclose : ‖M - N‖ ≤ ε) :
    ∀ x ∈ s, (g - ε) * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (M x) x) := by
  intro x hx
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hclose g) (sq_nonneg _)).trans
    (quadratic_lower_bound_sub_norm N M s g hgap x hx)

/-- Quantitative gap preservation for a perturbed row, conditional only on
the original gap and row bounds (`app:ch_response:cor:current-atoms`). -/
theorem normal_add_lower_bound (A D : E →L[𝕜] F) (s : Set F) {g a d : ℝ}
    (hgap : ∀ x ∈ s, g * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (normal A x) x))
    (hA : ‖A‖ ≤ a) (hD : ‖D‖ ≤ d) :
    ∀ x ∈ s, (g - (2 * a * d + d ^ 2)) * ‖x‖ ^ 2 ≤
      RCLike.re (inner 𝕜 (normal (A + D) x) x) :=
  quadratic_lower_bound_of_norm_sub_le _ _ s hgap
    (norm_normal_add_sub_le_of_bounds A D hA hD)

/-- An error at most half the original gap preserves half the gap
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem normal_add_half_gap (A D : E →L[𝕜] F) (s : Set F) {g a d : ℝ}
    (hgap : ∀ x ∈ s, g * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (normal A x) x))
    (hA : ‖A‖ ≤ a) (hD : ‖D‖ ≤ d) (hsmall : 2 * a * d + d ^ 2 ≤ g / 2) :
    ∀ x ∈ s, (g / 2) * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (normal (A + D) x) x) := by
  intro x hx
  have h := normal_add_lower_bound A D s hgap hA hD x hx
  have hcoeff : g / 2 ≤ g - (2 * a * d + d ^ 2) := by linarith
  exact (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)).trans h

end JanetCartan.NormalPerturbation
