module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.DiagonalTrace.WeightedSeries
public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# The bounded Fourier diagonal synthesis operator

The weighted Hilbert synthesis used in `app:ch_osc:lem:osc-amplitude`
is defined by its original convergent mode series. Its finite
regularizations converge in operator norm, with an explicit
inverse-weight tail bound. The individual mode operator norms need
not form a summable family.
-/

@[expose] public noncomputable section

open Filter
open scoped BigOperators ENNReal Topology

namespace JanetCartan.AmplitudeBound.DiagonalTrace

variable {κ H H' : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup H'] [NormedSpace ℂ H'] [CompleteSpace H']

omit [NormedSpace ℂ H] in
private theorem summable_lp_norm_sq (a : lp (fun _ : κ ↦ H) 2) :
    Summable (fun k ↦ ‖a k‖ ^ 2) := by
  simpa using (lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

omit [NormedSpace ℂ H] in
private theorem lp_norm_sq (a : lp (fun _ : κ ↦ H) 2) :
    ‖a‖ ^ 2 = ∑' k, ‖a k‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a

private theorem normalized_energy (w : ℝ) (hw : 0 < w) (a : H) :
    w * ‖(((Real.sqrt w)⁻¹ : ℝ) : ℂ) • a‖ ^ 2 = ‖a‖ ^ 2 := by
  have hnorm : ‖(((Real.sqrt w)⁻¹ : ℝ) : ℂ)‖ = (Real.sqrt w)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [norm_smul, hnorm, mul_pow, inv_pow, Real.sq_sqrt hw.le,
    ← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]

private theorem normalized_series_bound
    (w : κ → ℝ) (hw : ∀ k, 0 < w k)
    (hsum : Summable (fun k ↦ (w k)⁻¹))
    (M : κ → H →L[ℂ] H') (hM : ∀ k, ‖M k‖ ≤ 1)
    (a : lp (fun _ : κ ↦ H) 2) :
    Summable (fun k ↦ M k ((((Real.sqrt (w k))⁻¹ : ℝ) : ℂ) • a k)) ∧
      ‖∑' k, M k ((((Real.sqrt (w k))⁻¹ : ℝ) : ℂ) • a k)‖ ≤
        Real.sqrt (∑' k, (w k)⁻¹) * ‖a‖ := by
  have henergy : Summable (fun k ↦
      w k * ‖(((Real.sqrt (w k))⁻¹ : ℝ) : ℂ) • a k‖ ^ 2) := by
    simpa only [normalized_energy _ (hw _)] using summable_lp_norm_sq a
  have h := summable_weighted_mode_series w hw hsum M hM
    (fun k ↦ (((Real.sqrt (w k))⁻¹ : ℝ) : ℂ) • a k) henergy
  refine ⟨h.2.1, ?_⟩
  simpa only [normalized_energy _ (hw _), ← lp_norm_sq a,
    Real.sqrt_sq (norm_nonneg a)] using h.2.2

/-- The actual Sobolev diagonal synthesis in
`app:ch_osc:lem:osc-amplitude`, on the normalized weighted coefficient
space. The mode contractions are the original supplied operators. -/
def weightedSynthesis
    (w : κ → ℝ) (hw : ∀ k, 0 < w k)
    (hsum : Summable (fun k ↦ (w k)⁻¹))
    (M : κ → H →L[ℂ] H') (hM : ∀ k, ‖M k‖ ≤ 1) :
    lp (fun _ : κ ↦ H) 2 →L[ℂ] H' :=
  LinearMap.mkContinuous
    { toFun a := ∑' k, M k ((((Real.sqrt (w k))⁻¹ : ℝ) : ℂ) • a k)
      map_add' a b := by
        simp only [lp.coeFn_add, Pi.add_apply, smul_add, map_add]
        exact (normalized_series_bound w hw hsum M hM a).1.tsum_add
          (normalized_series_bound w hw hsum M hM b).1
      map_smul' z a := by
        change (∑' k, M k ((((Real.sqrt (w k))⁻¹ : ℝ) : ℂ) • (z • a k))) =
          z • (∑' k, M k ((((Real.sqrt (w k))⁻¹ : ℝ) : ℂ) • a k))
        calc
          _ = ∑' k, z • M k ((((Real.sqrt (w k))⁻¹ : ℝ) : ℂ) • a k) := by
            congr 1
            funext k
            rw [smul_comm, map_smul]
          _ = _ := (normalized_series_bound w hw hsum M hM a).1.tsum_const_smul z }
    (Real.sqrt (∑' k, (w k)⁻¹))
    (by
      intro a
      exact (normalized_series_bound w hw hsum M hM a).2)

/-- Evaluation of the bounded synthesis is precisely the original
convergent Fourier-mode series. -/
@[simp] theorem weightedSynthesis_apply
    (w : κ → ℝ) (hw : ∀ k, 0 < w k)
    (hsum : Summable (fun k ↦ (w k)⁻¹))
    (M : κ → H →L[ℂ] H') (hM : ∀ k, ‖M k‖ ≤ 1)
    (a : lp (fun _ : κ ↦ H) 2) :
    weightedSynthesis w hw hsum M hM a =
      ∑' k, M k ((((Real.sqrt (w k))⁻¹ : ℝ) : ℂ) • a k) := rfl

/-- The Sobolev diagonal constant is the square root of the sum of
inverse weights. -/
theorem norm_weightedSynthesis_le
    (w : κ → ℝ) (hw : ∀ k, 0 < w k)
    (hsum : Summable (fun k ↦ (w k)⁻¹))
    (M : κ → H →L[ℂ] H') (hM : ∀ k, ‖M k‖ ≤ 1) :
    ‖weightedSynthesis w hw hsum M hM‖ ≤ Real.sqrt (∑' k, (w k)⁻¹) := by
  exact (weightedSynthesis w hw hsum M hM).opNorm_le_bound
    (Real.sqrt_nonneg _) (fun a ↦ (normalized_series_bound w hw hsum M hM a).2)

/-- The literal finite-mode regularization of the weighted diagonal. -/
def weightedSynthesisPartial (w : κ → ℝ)
    (M : κ → H →L[ℂ] H') (s : Finset κ) : lp (fun _ : κ ↦ H) 2 →L[ℂ] H' :=
  ∑ k ∈ s, (((Real.sqrt (w k))⁻¹ : ℝ) : ℂ) •
    (M k).comp (lp.evalCLM ℂ (fun _ : κ ↦ H) 2 k)

omit [CompleteSpace H'] in
/-- Evaluation of the finite regularization uses the same original
mode operators as the full synthesis. -/
@[simp] theorem weightedSynthesisPartial_apply
    (w : κ → ℝ) (M : κ → H →L[ℂ] H') (s : Finset κ)
    (a : lp (fun _ : κ ↦ H) 2) :
    weightedSynthesisPartial w M s a =
      ∑ k ∈ s, M k ((((Real.sqrt (w k))⁻¹ : ℝ) : ℂ) • a k) := by
  simp [weightedSynthesisPartial, lp.evalCLM, lp.evalₗ, map_smul]
  rfl

omit [CompleteSpace H'] in
/-- Each finite diagonal regularization satisfies the finite inverse-weight
bound, uniformly over its normalized coefficient input. -/
theorem norm_weightedSynthesisPartial_le
    (w : κ → ℝ) (hw : ∀ k, 0 < w k)
    (M : κ → H →L[ℂ] H') (hM : ∀ k, ‖M k‖ ≤ 1) (s : Finset κ) :
    ‖weightedSynthesisPartial w M s‖ ≤ Real.sqrt (∑ k ∈ s, (w k)⁻¹) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro a
  have h := norm_finite_mode_sum_le w hw M hM
    (fun k ↦ (((Real.sqrt (w k))⁻¹ : ℝ) : ℂ) • a k) s
  have hsq : (∑ k ∈ s, ‖a k‖ ^ 2) ≤ ‖a‖ ^ 2 := by
    rw [lp_norm_sq a]
    exact (summable_lp_norm_sq a).sum_le_tsum s (fun k _ ↦ sq_nonneg _)
  have hsqrt : Real.sqrt (∑ k ∈ s, ‖a k‖ ^ 2) ≤ ‖a‖ := by
    simpa only [Real.sqrt_sq (norm_nonneg a)] using Real.sqrt_le_sqrt hsq
  simp only [normalized_energy _ (hw _)] at h
  simpa only [weightedSynthesisPartial_apply] using
    h.trans (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _))

/-- The inverse-weight tail controls the omitted actual diagonal
modes, uniformly on the unit ball of the coefficient space. -/
theorem norm_weightedSynthesis_sub_partial_apply_le
    (w : κ → ℝ) (hw : ∀ k, 0 < w k)
    (hsum : Summable (fun k ↦ (w k)⁻¹))
    (M : κ → H →L[ℂ] H') (hM : ∀ k, ‖M k‖ ≤ 1)
    (s : Finset κ) (a : lp (fun _ : κ ↦ H) 2) :
    ‖weightedSynthesis w hw hsum M hM a - weightedSynthesisPartial w M s a‖ ≤
      Real.sqrt (∑' k : {k // k ∉ s}, (w k)⁻¹) * ‖a‖ := by
  have henergy : Summable (fun k ↦
      w k * ‖(((Real.sqrt (w k))⁻¹ : ℝ) : ℂ) • a k‖ ^ 2) := by
    simpa only [normalized_energy _ (hw _)] using summable_lp_norm_sq a
  have htail := norm_mode_series_sub_sum_le w hw hsum M hM
    (fun k ↦ (((Real.sqrt (w k))⁻¹ : ℝ) : ℂ) • a k) henergy s
  have hsq : (∑' k : {k // k ∉ s}, ‖a k‖ ^ 2) ≤ ‖a‖ ^ 2 := by
    rw [lp_norm_sq a]
    exact Summable.tsum_subtype_le (fun k ↦ ‖a k‖ ^ 2) {k | k ∉ s}
      (fun k ↦ sq_nonneg _) (summable_lp_norm_sq a)
  have hsqrt : Real.sqrt (∑' k : {k // k ∉ s}, ‖a k‖ ^ 2) ≤ ‖a‖ := by
    simpa only [Real.sqrt_sq (norm_nonneg a)] using Real.sqrt_le_sqrt hsq
  simp only [normalized_energy _ (hw _)] at htail
  simpa only [weightedSynthesis_apply, weightedSynthesisPartial_apply] using
    htail.trans (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _))

/-- Operator-norm convergence has the same inverse-weight tail bound;
there is no hypothesis that the mode operator norms are summable. -/
theorem norm_weightedSynthesis_sub_partial_le
    (w : κ → ℝ) (hw : ∀ k, 0 < w k)
    (hsum : Summable (fun k ↦ (w k)⁻¹))
    (M : κ → H →L[ℂ] H') (hM : ∀ k, ‖M k‖ ≤ 1) (s : Finset κ) :
    ‖weightedSynthesis w hw hsum M hM - weightedSynthesisPartial w M s‖ ≤
      Real.sqrt (∑' k : {k // k ∉ s}, (w k)⁻¹) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  exact norm_weightedSynthesis_sub_partial_apply_le w hw hsum M hM s

/-- The actual finite Fourier-mode diagonals converge in operator norm
to the bounded synthesis in `app:ch_osc:lem:osc-amplitude`. -/
theorem tendsto_weightedSynthesisPartial
    (w : κ → ℝ) (hw : ∀ k, 0 < w k)
    (hsum : Summable (fun k ↦ (w k)⁻¹))
    (M : κ → H →L[ℂ] H') (hM : ∀ k, ‖M k‖ ≤ 1) :
    Tendsto (weightedSynthesisPartial w M) atTop
      (𝓝 (weightedSynthesis w hw hsum M hM)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have htail : Tendsto
      (fun s : Finset κ ↦ Real.sqrt (∑' k : {k // k ∉ s}, (w k)⁻¹))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (tendsto_tsum_compl_atTop_zero (fun k ↦ (w k)⁻¹)).sqrt
  apply squeeze_zero (fun s ↦ norm_nonneg _) _ htail
  intro s
  rw [norm_sub_rev]
  exact norm_weightedSynthesis_sub_partial_le w hw hsum M hM s

end JanetCartan.AmplitudeBound.DiagonalTrace
