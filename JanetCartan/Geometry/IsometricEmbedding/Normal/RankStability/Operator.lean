module

public import JanetCartan.Analysis.Operator.NormalPerturbation.Basic

import Mathlib.Tactic.Positivity

/-!
# Quantitative openness of surjective normal maps

Finite-dimensional estimates for `main:prop:seed` and
`app:ch_seed:setup:seed-current`. A least singular value `κ` becomes at least
`κ / 2` in the operator-norm ball of radius `κ / 2`; the normal Gram gap is
then at least `κ² / 4`. These statements concern maps between fixed spaces.
-/

@[expose] public noncomputable section

open ContinuousLinearMap

namespace JanetCartan.NormalRankStability

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `app:ch_seed:setup:seed-current`: full normal rank is equivalent to
injectivity of the adjoint. -/
theorem surjective_iff_adjoint_injective (B : E →L[ℝ] F) :
    Function.Surjective B ↔ Function.Injective B.adjoint := by
  constructor
  · intro hB
    apply (injective_iff_map_eq_zero _).2
    intro y hy
    obtain ⟨x, rfl⟩ := hB y
    have h := B.adjoint_inner_right x (B x)
    rw [hy, inner_zero_right] at h
    exact (inner_self_eq_zero).mp h.symm
  · intro hB
    have hi : Function.Injective (B.comp B.adjoint).toLinearMap :=
      B.self_comp_adjoint_injective_iff.mpr hB
    have hs := LinearMap.injective_iff_surjective.mp hi
    intro y
    obtain ⟨z, hz⟩ := hs y
    exact ⟨B.adjoint z, hz⟩

/-- `main:prop:seed`: surjectivity supplies a strictly positive least
normal singular value, including the zero-dimensional output case. -/
theorem exists_adjoint_lower_bound (B : E →L[ℝ] F) (hB : Function.Surjective B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ y, κ * ‖y‖ ≤ ‖B.adjoint y‖ := by
  obtain ⟨K, hK, hbound⟩ := B.adjoint.toLinearMap.injective_iff_antilipschitz.mp
    ((surjective_iff_adjoint_injective B).mp hB)
  have hK' : 0 < (K : ℝ) := hK
  refine ⟨(K : ℝ)⁻¹, inv_pos.mpr hK', fun y ↦ ?_⟩
  have h := ZeroHomClass.bound_of_antilipschitz B.adjoint hbound y
  calc
    (K : ℝ)⁻¹ * ‖y‖ ≤ (K : ℝ)⁻¹ * ((K : ℝ) * ‖B.adjoint y‖) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hK'.le)
    _ = ‖B.adjoint y‖ := by rw [← mul_assoc, inv_mul_cancel₀ hK'.ne', one_mul]

/-- `app:ch_seed:setup:seed-current`: a perturbation loses at most its
operator norm from the least normal singular value. -/
theorem adjoint_lower_bound_sub_norm (B C : E →L[ℝ] F) {κ : ℝ}
    (hgap : ∀ y, κ * ‖y‖ ≤ ‖B.adjoint y‖) (y : F) :
    (κ - ‖C - B‖) * ‖y‖ ≤ ‖C.adjoint y‖ := by
  have h := (B.adjoint - C.adjoint).le_opNorm y
  have hn : ‖B.adjoint - C.adjoint‖ = ‖C - B‖ := by
    rw [← map_sub, LinearIsometryEquiv.norm_map, norm_sub_rev]
  rw [hn, sub_apply] at h
  have ht := norm_sub_norm_le (B.adjoint y) (C.adjoint y)
  nlinarith [hgap y]

/-- `app:ch_seed:setup:seed-current`: the Gram quadratic form is the
squared norm of the adjoint. -/
theorem normal_inner_eq_norm_adjoint_sq (B : E →L[ℝ] F) (y : F) :
    inner ℝ (NormalPerturbation.normal B y) y = ‖B.adjoint y‖ ^ 2 := by
  simpa [NormalPerturbation.normal] using
    (B.adjoint.apply_norm_sq_eq_inner_adjoint_left y).symm

/-- `app:ch_seed:setup:seed-current`: a positive adjoint lower bound
implies full normal rank and its squared Gram gap. -/
theorem surjective_and_normal_gap_of_adjoint_lower_bound (B : E →L[ℝ] F)
    {κ : ℝ} (hκ : 0 < κ) (hgap : ∀ y, κ * ‖y‖ ≤ ‖B.adjoint y‖) :
    Function.Surjective B ∧
      ∀ y, κ ^ 2 * ‖y‖ ^ 2 ≤ inner ℝ (NormalPerturbation.normal B y) y := by
  constructor
  · apply (surjective_iff_adjoint_injective B).mpr
    apply (injective_iff_map_eq_zero _).2
    intro y hy
    have h := hgap y
    rw [hy, norm_zero] at h
    have : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
    exact norm_eq_zero.mp this
  · intro y
    rw [normal_inner_eq_norm_adjoint_sq]
    have h := mul_self_le_mul_self (by positivity : 0 ≤ κ * ‖y‖) (hgap y)
    nlinarith

/-- `app:ch_seed:setup:seed-current`: a radius `κ / 2` preserves
surjectivity and the explicit Gram lower bound `κ² / 4`. -/
theorem surjective_and_normal_gap_of_norm_sub_le (B C : E →L[ℝ] F)
    {κ : ℝ} (hκ : 0 < κ) (hgap : ∀ y, κ * ‖y‖ ≤ ‖B.adjoint y‖)
    (hclose : ‖C - B‖ ≤ κ / 2) :
    Function.Surjective C ∧
      ∀ y, (κ ^ 2 / 4) * ‖y‖ ^ 2 ≤ inner ℝ (NormalPerturbation.normal C y) y := by
  have hb (y : F) : κ / 2 * ‖y‖ ≤ ‖C.adjoint y‖ := by
    have h := adjoint_lower_bound_sub_norm B C hgap y
    have hm := mul_le_mul_of_nonneg_right hclose (norm_nonneg y)
    nlinarith
  convert surjective_and_normal_gap_of_adjoint_lower_bound C (by positivity) hb using 1
  ring_nf

/-- `main:prop:seed`: full rank has a concrete neighborhood with a
uniform positive normal Gram gap. The radius equals half a valid least
singular value, and the resulting Gram gap equals the radius squared. -/
theorem exists_surjective_normal_gap_neighborhood (B : E →L[ℝ] F)
    (hB : Function.Surjective B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ C : E →L[ℝ] F, ‖C - B‖ ≤ κ / 2 →
      Function.Surjective C ∧ ∀ y,
        (κ ^ 2 / 4) * ‖y‖ ^ 2 ≤ inner ℝ (NormalPerturbation.normal C y) y := by
  obtain ⟨κ, hκ, hg⟩ := exists_adjoint_lower_bound B hB
  exact ⟨κ, hκ, fun C hc ↦ surjective_and_normal_gap_of_norm_sub_le B C hκ hg hc⟩

end JanetCartan.NormalRankStability
