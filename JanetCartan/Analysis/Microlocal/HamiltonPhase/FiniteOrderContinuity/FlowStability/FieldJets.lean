module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.FlowStability.LowOrder

/-!
# Field jets evaluated along different trajectories

Coefficient inputs for the spatial-flow induction in
`app:lem:common-hamilton-phase`. The perturbation seminorm has exactly the
requested order. The extra derivative in the displacement bound belongs only
to the fixed smooth reference field.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff NNReal

namespace JanetCartan.ODE

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `app:lem:common-hamilton-phase`: same-point field jet differences are
controlled by the perturbation seminorm, with no loss of derivatives. -/
theorem norm_field_jet_sub_le_cNorm {V V₀ : E → F} {S U : Set E}
    (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U)
    (hV : ContDiffOn ℝ ∞ V U) (hV₀ : ContDiffOn ℝ ∞ V₀ U)
    {m j : ℕ} (hj : j ≤ m) {y : E} (hy : y ∈ S) :
    ‖iteratedFDeriv ℝ j V y - iteratedFDeriv ℝ j V₀ y‖ ≤ cNorm S m (V - V₀) := by
  rw [← iteratedFDeriv_sub_apply
    ((hV.contDiffAt (hU.mem_nhds (hSU hy))).of_le (by simp))
    ((hV₀.contDiffAt (hU.mem_nhds (hSU hy))).of_le (by simp))]
  exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hS
    (fun y hy ↦ ((hV.sub hV₀).contDiffAt (hU.mem_nhds (hSU hy))).of_le (by simp)) hy hj

/-- `app:lem:common-hamilton-phase`: the fixed reference field's next derivative
bounds displacement of its `j`th jet on a compact convex state set. -/
theorem norm_field_jet_displacement_le {V₀ : E → F} {S U : Set E}
    (hS : IsCompact S) (hconv : Convex ℝ S) (hU : IsOpen U) (hSU : S ⊆ U)
    (hV₀ : ContDiffOn ℝ ∞ V₀ U) (j : ℕ) {y y₀ : E} (hy : y ∈ S) (hy₀ : y₀ ∈ S) :
    ‖iteratedFDeriv ℝ j V₀ y - iteratedFDeriv ℝ j V₀ y₀‖ ≤
      cNorm S (j + 1) V₀ * ‖y - y₀‖ := by
  have hs z (hz : z ∈ S) : ContDiffAt ℝ ∞ V₀ z :=
    hV₀.contDiffAt (hU.mem_nhds (hSU hz))
  apply hconv.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ ((hs z hz).iteratedFDeriv_right (m := 1) (by simp)).differentiableAt
      (by simp)) _ hy₀ hy
  intro z hz
  rw [norm_fderiv_iteratedFDeriv]
  exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hS
    (fun z hz ↦ (hs z hz).of_le (by simp)) hz le_rfl

/-- `app:lem:common-hamilton-phase`: field jets along two actual trajectories
are controlled by the field perturbation and trajectory displacement. The
spatial induction supplies that displacement by its order-zero case. -/
theorem norm_field_jet_sub_le_cNorm_add {V V₀ : E → F} {S U : Set E}
    (hS : IsCompact S) (hconv : Convex ℝ S) (hU : IsOpen U) (hSU : S ⊆ U)
    (hV : ContDiffOn ℝ ∞ V U) (hV₀ : ContDiffOn ℝ ∞ V₀ U)
    {m j : ℕ} (hj : j ≤ m) {y y₀ : E} (hy : y ∈ S) (hy₀ : y₀ ∈ S) :
    ‖iteratedFDeriv ℝ j V y - iteratedFDeriv ℝ j V₀ y₀‖ ≤
      cNorm S m (V - V₀) + cNorm S (m + 1) V₀ * ‖y - y₀‖ := by
  calc
    _ ≤ ‖iteratedFDeriv ℝ j V y - iteratedFDeriv ℝ j V₀ y‖ +
        ‖iteratedFDeriv ℝ j V₀ y - iteratedFDeriv ℝ j V₀ y₀‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ cNorm S m (V - V₀) + cNorm S (j + 1) V₀ * ‖y - y₀‖ :=
      add_le_add (norm_field_jet_sub_le_cNorm hS hU hSU hV hV₀ hj hy)
        (norm_field_jet_displacement_le hS hconv hU hSU hV₀ j hy hy₀)
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (cNorm_mono_order (Nat.add_le_add_right hj 1)) (norm_nonneg _))

end JanetCartan.ODE
