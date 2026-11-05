module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecificLimits.Normed

import Mathlib.Tactic.Linarith

/-!
# The base-space Neumann inverse

The series in `app:ch_regular:eq:neumann-series` is formed once in the bounded
operator algebra on a real Banach space (in particular, on the base Hilbert space).
-/

@[expose] public noncomputable section

namespace JanetCartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The single base-space operator from `app:ch_regular:eq:neumann-series`.
Its inverse identities require `‖K‖ < 1`. -/
def neumannInverse (K : E →L[ℝ] E) : E →L[ℝ] E := ∑' n : ℕ, (-K) ^ n

/-- Operator-norm convergence of `app:ch_regular:eq:neumann-series`. -/
theorem hasSum_neumannInverse (K : E →L[ℝ] E) (hK : ‖K‖ < 1) :
    HasSum (fun n : ℕ ↦ (-K) ^ n) (neumannInverse K) :=
  (summable_geometric_of_norm_lt_one (by simpa using hK : ‖-K‖ < 1)).hasSum

/-- Right inverse identity in `app:ch_regular:thm:exact-correction`. -/
theorem add_mul_neumannInverse (K : E →L[ℝ] E) (hK : ‖K‖ < 1) :
    (1 + K) * neumannInverse K = 1 := by
  simpa [neumannInverse] using mul_neg_geom_series (-K) (by simpa using hK)

/-- Left inverse identity in `app:ch_regular:thm:exact-correction`. -/
theorem neumannInverse_mul_add (K : E →L[ℝ] E) (hK : ‖K‖ < 1) :
    neumannInverse K * (1 + K) = 1 := by
  simpa [neumannInverse] using geom_series_mul_neg (-K) (by simpa using hK)

/-- The equation used to bootstrap regularity in
`app:ch_regular:thm:exact-correction`. -/
theorem neumannInverse_eq_sub (K : E →L[ℝ] E) (hK : ‖K‖ < 1) (f : E) :
    neumannInverse K f = f - K (neumannInverse K f) := by
  have h := congrArg (fun A : E →L[ℝ] E ↦ A f) (add_mul_neumannInverse K hK)
  change neumannInverse K f + K (neumannInverse K f) = f at h
  exact eq_sub_of_add_eq h

/-- Uniqueness on the entire base space, so inverses cannot vary with Sobolev
order (`app:ch_regular:thm:exact-correction`). -/
theorem eq_neumannInverse_of_add_eq (K : E →L[ℝ] E) (hK : ‖K‖ < 1)
    {z f : E} (hz : z + K z = f) : z = neumannInverse K f := by
  have h := congrArg (fun A : E →L[ℝ] E ↦ A z) (neumannInverse_mul_add K hK)
  change neumannInverse K (z + K z) = z at h
  rw [hz] at h
  exact h.symm

/-- The uniform base estimate `(1-θ)⁻¹` from
`app:ch_regular:thm:exact-correction`. -/
theorem norm_neumannInverse_apply_le (K : E →L[ℝ] E) {θ : ℝ}
    (hK : ‖K‖ ≤ θ) (hθ : θ < 1) (f : E) :
    ‖neumannInverse K f‖ ≤ (1 - θ)⁻¹ * ‖f‖ := by
  have h := norm_sub_le f (K (neumannInverse K f))
  rw [← neumannInverse_eq_sub K (hK.trans_lt hθ) f] at h
  have hbound := (K.le_opNorm (neumannInverse K f)).trans
    (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  have hmul : ‖neumannInverse K f‖ * (1 - θ) ≤ ‖f‖ := by nlinarith
  simpa [div_eq_mul_inv, mul_comm] using (le_div_iff₀ (sub_pos.mpr hθ)).mpr hmul

/-- The base operator norm estimate in `app:ch_regular:thm:exact-correction`. -/
theorem norm_neumannInverse_le (K : E →L[ℝ] E) {θ : ℝ}
    (hK : ‖K‖ ≤ θ) (hθ : θ < 1) : ‖neumannInverse K‖ ≤ (1 - θ)⁻¹ := by
  exact (neumannInverse K).opNorm_le_bound (inv_nonneg.mpr (sub_nonneg.mpr hθ.le))
    (norm_neumannInverse_apply_le K hK hθ)

end JanetCartan
