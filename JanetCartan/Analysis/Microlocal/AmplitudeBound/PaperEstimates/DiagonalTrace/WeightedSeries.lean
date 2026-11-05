module

public import JanetCartan.Analysis.Fourier.Periodic.Interpolation.Summation
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Weighted mode summation for the Sobolev diagonal

The Hilbert-valued diagonal step in `app:ch_osc:lem:osc-amplitude` uses
Cauchy–Schwarz in the Fourier index, before the original mode operators
are summed. This file proves convergence as well as the bound. In
particular, no summability of the mode operator norms is assumed.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan.AmplitudeBound.DiagonalTrace

variable {κ H H' : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup H'] [NormedSpace ℂ H'] [CompleteSpace H']

omit [CompleteSpace H'] in
private theorem mode_norm_sq_le (w : ℝ) (hw : 0 < w)
    (M : H →L[ℂ] H') (hM : ‖M‖ ≤ 1) (a : H) :
    ‖M a‖ ^ 2 ≤ w⁻¹ * (w * ‖a‖ ^ 2) := by
  have hnorm : ‖M a‖ ≤ ‖a‖ :=
    (M.le_opNorm a).trans (by simpa using mul_le_mul_of_nonneg_right hM (norm_nonneg a))
  calc
    ‖M a‖ ^ 2 ≤ ‖a‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
    _ = w⁻¹ * (w * ‖a‖ ^ 2) := by rw [← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul]

/-- The direct weighted coefficient estimate underlying
`app:ch_osc:eq:amplitude-row`. It proves absolute convergence of the
original mode series and its square-root energy bound. -/
theorem summable_weighted_mode_series
    (w : κ → ℝ) (hw : ∀ k, 0 < w k)
    (hsum : Summable (fun k ↦ (w k)⁻¹))
    (M : κ → H →L[ℂ] H') (hM : ∀ k, ‖M k‖ ≤ 1)
    (a : κ → H) (ha : Summable (fun k ↦ w k * ‖a k‖ ^ 2)) :
    Summable (fun k ↦ ‖M k (a k)‖) ∧
      Summable (fun k ↦ M k (a k)) ∧
      ‖∑' k, M k (a k)‖ ≤
        Real.sqrt (∑' k, (w k)⁻¹) * Real.sqrt (∑' k, w k * ‖a k‖ ^ 2) := by
  obtain ⟨habs, hbound⟩ := summable_and_tsum_le_sqrt_mul_sqrt
    (t := fun k ↦ ‖M k (a k)‖)
    (a := fun k ↦ (w k)⁻¹) (b := fun k ↦ w k * ‖a k‖ ^ 2)
    (fun k ↦ norm_nonneg _) (fun k ↦ inv_nonneg.mpr (hw k).le)
    (fun k ↦ mul_nonneg (hw k).le (sq_nonneg _))
    (fun k ↦ mode_norm_sq_le (w k) (hw k) (M k) (hM k) (a k)) hsum ha
  exact ⟨habs, habs.of_norm, (norm_tsum_le_tsum_norm habs).trans hbound⟩

omit [CompleteSpace H'] in
/-- The finite Fourier-mode diagonal bound, with precisely the weights
and coefficient energy on the selected finite set. -/
theorem norm_finite_mode_sum_le
    (w : κ → ℝ) (hw : ∀ k, 0 < w k)
    (M : κ → H →L[ℂ] H') (hM : ∀ k, ‖M k‖ ≤ 1)
    (a : κ → H) (s : Finset κ) :
    ‖∑ k ∈ s, M k (a k)‖ ≤
      Real.sqrt (∑ k ∈ s, (w k)⁻¹) * Real.sqrt (∑ k ∈ s, w k * ‖a k‖ ^ 2) := by
  have hsq := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun k _ ↦ inv_nonneg.mpr (hw k).le)
    (fun k _ ↦ mul_nonneg (hw k).le (sq_nonneg ‖a k‖))
    (fun k _ ↦ mode_norm_sq_le (w k) (hw k) (M k) (hM k) (a k))
  exact (norm_sum_le _ _).trans ((Real.le_sqrt_of_sq_le hsq).trans_eq
    (Real.sqrt_mul (Finset.sum_nonneg (fun k _ ↦ inv_nonneg.mpr (hw k).le)) _))

/-- The actual omitted mode series has a norm bound involving the
inverse-weight tail. This is the convergence estimate used for the
finite regularizations in `app:ch_osc:lem:osc-amplitude`. -/
theorem norm_mode_series_sub_sum_le
    (w : κ → ℝ) (hw : ∀ k, 0 < w k)
    (hsum : Summable (fun k ↦ (w k)⁻¹))
    (M : κ → H →L[ℂ] H') (hM : ∀ k, ‖M k‖ ≤ 1)
    (a : κ → H) (ha : Summable (fun k ↦ w k * ‖a k‖ ^ 2)) (s : Finset κ) :
    ‖(∑' k, M k (a k)) - ∑ k ∈ s, M k (a k)‖ ≤
      Real.sqrt (∑' k : {k // k ∉ s}, (w k)⁻¹) *
        Real.sqrt (∑' k : {k // k ∉ s}, w k * ‖a k‖ ^ 2) := by
  have hfull := summable_weighted_mode_series w hw hsum M hM a ha
  have htail := summable_weighted_mode_series
    (fun k : {k // k ∉ s} ↦ w k) (fun k ↦ hw k)
    (hsum.subtype (fun k ↦ k ∉ s))
    (fun k ↦ M k) (fun k ↦ hM k) (fun k ↦ a k)
    (ha.subtype (fun k ↦ k ∉ s))
  rw [← hfull.2.1.sum_add_tsum_subtype_compl s, add_sub_cancel_left]
  exact htail.2.2

end JanetCartan.AmplitudeBound.DiagonalTrace
