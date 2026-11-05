module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.ScalarTerms

/-!
# Slow directional coefficient derivatives

Normalize the one slow-scale factor before applying the scalar multiplier.
This is the coefficient-derivative term of
`app:ch_response:eq:response-graded-derivative`.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.IsometricEmbedding.Reconstruction
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The normalized coefficient derivative used in
`app:ch_response:eq:response-reconstruction-grading`. Its extracted factor `L`
is restored in the physical derivative sum. -/
def reconstructionNormalizedDirectionalCoefficient (L : ℝ) (c : E → ℂ) (v : E) : E → ℂ :=
  fun x ↦ (L⁻¹ : ℝ) • fderiv ℝ c x v

/-- Local smoothness suffices for the normalized derivative multiplier in
`app:ch_response:eq:response-graded-derivative`. -/
theorem reconstructionNormalizedDirectionalCoefficient_contDiffOn
    {Ω : Set E} (hΩ : IsOpen Ω) {c : E → ℂ} (hc : ContDiffOn ℝ ∞ c Ω)
    (L : ℝ) (v : E) :
    ContDiffOn ℝ ∞ (reconstructionNormalizedDirectionalCoefficient L c v) Ω := by
  unfold reconstructionNormalizedDirectionalCoefficient
  exact (contDiffOn_const (c := (L⁻¹ : ℝ))).smul ((hc.fderiv_of_isOpen (m := ∞) hΩ (by simp)).clm_apply contDiffOn_const)

/-- The normalized coefficient derivative has a scale-independent shifted
primitive budget (`app:ch_response:eq:response-reconstruction-grading`). -/
theorem reconstructionNormalizedDirectionalCoefficient_budget
    {Ω : Set E} (hΩ : IsOpen Ω) {c : E → ℂ} (hc : ContDiffOn ℝ ∞ c Ω)
    (C : ℕ → ℝ) {L : ℝ} (hL : 0 < L) (m : ℕ)
    (hcB : ∀ r, r ≤ m + 1 → ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r c x‖ ≤ C r * L ^ r)
    (v : E) (hv : ‖v‖ ≤ 1) (r : ℕ) (hr : r ≤ m) (x : E) (hx : x ∈ Ω) :
    ‖iteratedFDeriv ℝ r (reconstructionNormalizedDirectionalCoefficient L c v) x‖ ≤
      C (r + 1) * L ^ r := by
  have hd : ContDiffAt ℝ r (fun y ↦ fderiv ℝ c y v) x :=
    (((hc.contDiffAt (hΩ.mem_nhds hx)).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiffAt_const).of_le (by simp)
  change ‖iteratedFDeriv ℝ r ((L⁻¹ : ℝ) • fun y ↦ fderiv ℝ c y v) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply hd, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hL)]
  apply (mul_le_mul_of_nonneg_left
    (reconstructionDirectionalCoefficient_budget hΩ hc C m hcB v hv r hr x hx)
    (inv_nonneg.mpr hL.le)).trans_eq
  field_simp

end JanetCartan.IsometricEmbedding.Reconstruction
