module

public import JanetCartan.Analysis.ContDiff.Norm.Defs
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Derivative bounds from values on inward segments

The local analytic step for `app:lem:elementary-interpolation-jets` in paper.tex.
All estimates use segments inside the ball and apply to arbitrary normed codomains.
-/

public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.CNormInterpolation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Appendix B, `app:lem:elementary-interpolation-jets`: a quadratic bound
for the first-order Taylor remainder on a convex set, without completeness. -/
theorem norm_sub_linearization_le {s : Set E} (hs : Convex ℝ s)
    {g : E → F} (hg : Differentiable ℝ g)
    (hg' : Differentiable ℝ (fderiv ℝ g)) {M : ℝ}
    (hM : ∀ z ∈ s, ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ M)
    {y z : E} (hy : y ∈ s) (hz : z ∈ s) :
    ‖g z - g y - fderiv ℝ g y (z - y)‖ ≤ M * ‖z - y‖ ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg (fderiv ℝ (fderiv ℝ g) y)).trans (hM y hy)
  have hseg := hs.segment_subset hy hz
  have hderiv : ∀ w ∈ segment ℝ y z,
      HasFDerivWithinAt (fun w ↦ g w - g y - fderiv ℝ g y (w - y))
        (fderiv ℝ g w - fderiv ℝ g y) (segment ℝ y z) w := by
    intro w _
    exact (((hg w).hasFDerivAt.sub_const _).sub
      ((fderiv ℝ g y).hasFDerivAt.comp w
        ((hasFDerivAt_id w).sub_const y))).hasFDerivWithinAt
  have hbound : ∀ w ∈ segment ℝ y z,
      ‖fderiv ℝ g w - fderiv ℝ g y‖ ≤ M * ‖z - y‖ := by
    intro w hw
    exact ((hs.norm_image_sub_le_of_norm_fderiv_le (fun w _ ↦ hg' w) hM hy
      (hseg hw)).trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hw) hM0))
  have h := (convex_segment y z).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hderiv hbound (left_mem_segment ℝ y z) (right_mem_segment ℝ y z)
  simpa [pow_two, mul_assoc] using h

/-- Appendix B, `app:lem:elementary-interpolation-jets`: the derivative at a
point of a closed ball is bounded using values along two inward segments.
The scale and constants are uniform in the function and the evaluation point. -/
theorem norm_fderiv_le_of_closedBall {x y : E} {ρ t M₀ M₂ : ℝ}
    (hρ : 0 < ρ) (ht : 0 < t) (ht1 : t ≤ 1)
    {g : E → F} (hg : Differentiable ℝ g)
    (hg' : Differentiable ℝ (fderiv ℝ g))
    (h₀ : ∀ z ∈ Metric.closedBall x ρ, ‖g z‖ ≤ M₀)
    (h₂ : ∀ z ∈ Metric.closedBall x ρ, ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ M₂)
    (hy : y ∈ Metric.closedBall x ρ) :
    ‖fderiv ℝ g y‖ ≤ 2 / (t * ρ) * M₀ + 5 * (t * ρ) * M₂ := by
  have hM₀ : 0 ≤ M₀ := (norm_nonneg (g y)).trans (h₀ y hy)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg (fderiv ℝ (fderiv ℝ g) y)).trans (h₂ y hy)
  have hxy : ‖x - y‖ ≤ ρ := by simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hy
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let z₀ := (1 - t) • y + t • x
  let z₁ := (1 - t) • y + t • (x + ρ • v)
  have hx : x ∈ Metric.closedBall x ρ := Metric.mem_closedBall_self hρ.le
  have hxv : x + ρ • v ∈ Metric.closedBall x ρ := by
    simp [Metric.mem_closedBall, dist_eq_norm, norm_smul, abs_of_pos hρ, hv]
  have hz₀ : z₀ ∈ Metric.closedBall x ρ :=
    (convex_closedBall x ρ) hy hx (by linarith) ht.le (by ring)
  have hz₁ : z₁ ∈ Metric.closedBall x ρ :=
    (convex_closedBall x ρ) hy hxv (by linarith) ht.le (by ring)
  have he₀ : z₀ - y = t • (x - y) := by dsimp [z₀]; module
  have he₁ : z₁ - y = t • (x - y + ρ • v) := by dsimp [z₁]; module
  have hd₀ : ‖z₀ - y‖ ≤ t * ρ := by
    rw [he₀, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left hxy ht.le
  have hd₁ : ‖z₁ - y‖ ≤ 2 * (t * ρ) := by
    rw [he₁, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have h := norm_add_le (x - y) (ρ • v)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, hv, mul_one] at h
    nlinarith [mul_le_mul_of_nonneg_left h ht.le]
  let r := fun z ↦ g z - g y - fderiv ℝ g y (z - y)
  have hr₀ : ‖r z₀‖ ≤ M₂ * (t * ρ) ^ 2 := by
    apply (norm_sub_linearization_le (convex_closedBall x ρ) hg hg' h₂ hy hz₀).trans
    gcongr
  have hr₁ : ‖r z₁‖ ≤ M₂ * (2 * (t * ρ)) ^ 2 := by
    apply (norm_sub_linearization_le (convex_closedBall x ρ) hg hg' h₂ hy hz₁).trans
    gcongr
  have heq : (t * ρ) • fderiv ℝ g y v = g z₁ - g z₀ - (r z₁ - r z₀) := by
    have hz : z₁ - y - (z₀ - y) = (t * ρ) • v := by dsimp [z₀, z₁]; module
    rw [← map_smul, ← hz, map_sub]
    dsimp [r]
    abel
  have hb : (t * ρ) * ‖fderiv ℝ g y v‖ ≤ 2 * M₀ + 5 * (t * ρ) ^ 2 * M₂ := by
    calc
      _ = ‖(t * ρ) • fderiv ℝ g y v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos ht hρ)]
      _ ≤ (‖g z₁‖ + ‖g z₀‖) + (‖r z₁‖ + ‖r z₀‖) := by
        rw [heq]
        exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))
      _ ≤ _ := by nlinarith [h₀ z₀ hz₀, h₀ z₁ hz₁]
  have hb' : ‖fderiv ℝ g y v‖ ≤ (2 * M₀ + 5 * (t * ρ) ^ 2 * M₂) / (t * ρ) :=
    (le_div_iff₀ (mul_pos ht hρ)).mpr (by nlinarith [hb])
  convert hb' using 1
  field_simp

section Iterated

variable (n : ℕ)

-- These aliases also keep instance synthesis for the nested operator spaces small.
local instance : NormedAddCommGroup (E [×n]→L[ℝ] F) := inferInstance
local instance : NormedSpace ℝ (E [×n]→L[ℝ] F) := inferInstance

/-- Appendix B, `app:lem:elementary-interpolation-jets`: the second derivative
of the nth derivative has the norm of the (n+2)nd derivative. -/
theorem norm_fderiv_fderiv_iteratedFDeriv (f : E → F) (y : E) :
    ‖fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ n f)) y‖ =
      ‖iteratedFDeriv ℝ (n + 2) f y‖ := by
  rw [fderiv_iteratedFDeriv, ← norm_iteratedFDeriv_one,
    LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_one,
    norm_fderiv_iteratedFDeriv]

/-- Appendix B, `app:lem:elementary-interpolation-jets`: consecutive derivatives
satisfy a two-term scale estimate on a closed ball. -/
theorem norm_iteratedFDeriv_succ_le_of_closedBall {x y : E} {ρ t M₀ M₂ : ℝ}
    (hρ : 0 < ρ) (ht : 0 < t) (ht1 : t ≤ 1)
    {f : E → F} (hf : ContDiff ℝ ∞ f)
    (h₀ : ∀ z ∈ Metric.closedBall x ρ, ‖iteratedFDeriv ℝ n f z‖ ≤ M₀)
    (h₂ : ∀ z ∈ Metric.closedBall x ρ, ‖iteratedFDeriv ℝ (n + 2) f z‖ ≤ M₂)
    (hy : y ∈ Metric.closedBall x ρ) :
    ‖iteratedFDeriv ℝ (n + 1) f y‖ ≤ 2 / (t * ρ) * M₀ + 5 * (t * ρ) * M₂ := by
  have hg : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := hf.iteratedFDeriv_right (by simp)
  rw [← norm_fderiv_iteratedFDeriv]
  apply norm_fderiv_le_of_closedBall hρ ht ht1 (hg.differentiable (by simp))
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) h₀ _ hy
  intro z hz
  rw [norm_fderiv_fderiv_iteratedFDeriv]
  exact h₂ z hz

end Iterated

/-- The supremum of the norm of one derivative, a summand in `cNorm`. -/
@[expose] def derivativeSup (s : Set E) (n : ℕ) (f : E → F) : ℝ :=
  sSup ((fun y ↦ ‖iteratedFDeriv ℝ n f y‖) '' s)

/-- Appendix B, `app:lem:elementary-interpolation-jets`: derivative suprema
are nonnegative. -/
theorem derivativeSup_nonneg (s : Set E) (n : ℕ) (f : E → F) :
    0 ≤ derivativeSup s n f := by
  apply Real.sSup_nonneg
  rintro _ ⟨y, _, rfl⟩
  exact norm_nonneg _

/-- Appendix B, `app:lem:elementary-interpolation-jets`: compactness bounds
the derivative images of a smooth function. -/
theorem norm_iteratedFDeriv_le_derivativeSup {s : Set E} (hs : IsCompact s)
    {f : E → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) {y : E} (hy : y ∈ s) :
    ‖iteratedFDeriv ℝ n f y‖ ≤ derivativeSup s n f := by
  apply le_csSup _ (mem_image_of_mem _ hy)
  exact (hs.image (hf.continuous_iteratedFDeriv (by simp)).norm).bddAbove

/-- Appendix B, `app:lem:elementary-interpolation-jets`: the uniform scale
estimate for three consecutive derivative suprema on a finite-dimensional ball. -/
theorem derivativeSup_succ_le [FiniteDimensional ℝ E] (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    {f : E → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    derivativeSup (Metric.closedBall x ρ) (n + 1) f ≤
      2 / (t * ρ) * derivativeSup (Metric.closedBall x ρ) n f +
        5 * (t * ρ) * derivativeSup (Metric.closedBall x ρ) (n + 2) f := by
  apply csSup_le
  · exact (Metric.nonempty_closedBall.mpr hρ.le).image _
  rintro _ ⟨y, hy, rfl⟩
  exact norm_iteratedFDeriv_succ_le_of_closedBall n hρ ht ht1 hf
    (fun _ hz ↦ norm_iteratedFDeriv_le_derivativeSup (isCompact_closedBall x ρ) hf n hz)
    (fun _ hz ↦ norm_iteratedFDeriv_le_derivativeSup (isCompact_closedBall x ρ) hf (n + 2) hz)
    hy

/-- Appendix B, `app:lem:elementary-interpolation-jets`: each derivative
supremum occurs as a nonnegative summand of the C-norm. -/
theorem derivativeSup_le_cNorm (s : Set E) (f : E → F) {n k : ℕ} (hnk : n ≤ k) :
    derivativeSup s n f ≤ cNorm s k f := by
  exact Finset.single_le_sum (fun i _ ↦ derivativeSup_nonneg s i f)
    (Finset.mem_range.mpr (by omega))

/-- Appendix B, `app:lem:elementary-interpolation-jets`: a uniform adjacent-order
scale estimate for the C-norm. This is the analytic input to finite-sequence
interpolation; its constant is independent of the derivative order and function. -/
theorem cNorm_succ_le_scale [FiniteDimensional ℝ E] (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    {f : E → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    cNorm (Metric.closedBall x ρ) (n + 1) f ≤
      (1 + 2 / ρ + 5 * ρ) *
        (t⁻¹ * cNorm (Metric.closedBall x ρ) n f +
          t * cNorm (Metric.closedBall x ρ) (n + 2) f) := by
  let s := Metric.closedBall x ρ
  have hnonneg : ∀ i, 0 ≤ cNorm s i f := by
    intro i
    exact Finset.sum_nonneg (fun j _ ↦ derivativeSup_nonneg s j f)
  have hstep : cNorm s (n + 1) f = cNorm s n f + derivativeSup s (n + 1) f :=
    Finset.sum_range_succ _ _
  have hadj := derivativeSup_succ_le x hρ hf n ht ht1
  have h₀ := derivativeSup_le_cNorm s f (n := n) (k := n) le_rfl
  have h₂ := derivativeSup_le_cNorm s f (n := n + 2) (k := n + 2) le_rfl
  have hlow : cNorm s n f ≤ t⁻¹ * cNorm s n f := by
    have hi : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
    simpa using mul_le_mul_of_nonneg_right hi (hnonneg n)
  have hb : cNorm s (n + 1) f ≤
      (1 + 2 / ρ) * (t⁻¹ * cNorm s n f) + 5 * ρ * (t * cNorm s (n + 2) f) := by
    rw [hstep]
    calc
      _ ≤ t⁻¹ * cNorm s n f +
          (2 / (t * ρ) * cNorm s n f + 5 * (t * ρ) * cNorm s (n + 2) f) := by
        apply add_le_add hlow
        exact hadj.trans (add_le_add (mul_le_mul_of_nonneg_left h₀ (by positivity))
          (mul_le_mul_of_nonneg_left h₂ (by positivity)))
      _ = _ := by field_simp; ring
  apply hb.trans
  have hA : 0 ≤ 1 + 2 / ρ := by positivity
  have hB : 0 ≤ 5 * ρ := by positivity
  have hL : 0 ≤ t⁻¹ * cNorm s n f := mul_nonneg (inv_nonneg.mpr ht.le) (hnonneg n)
  have hH : 0 ≤ t * cNorm s (n + 2) f := mul_nonneg ht.le (hnonneg (n + 2))
  dsimp [s] at *
  nlinarith [mul_nonneg hA hH, mul_nonneg hB hL]

end JanetCartan.CNormInterpolation
