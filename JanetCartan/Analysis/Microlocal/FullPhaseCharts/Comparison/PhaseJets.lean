module

public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# The phase jet budget for chart comparison

These are the input estimates for the comparison paragraph following
`app:ch_seed:eq:seed-quotient-integral`. They apply to the joint phase error
`S - S₀`, with physical and covector variables in its domain. In particular,
the Hessian and its next two joint derivatives are controlled by `cNorm K 4`.
They do not assume bounds for the quotient or its averaged gradient.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.FullPhaseCharts.Comparison

variable {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The joint phase differential costs one derivative in the `C⁴` input
budget of `app:ch_seed:prop:seed-phase-charts`. -/
theorem norm_phaseDifferential_jet_le_cNorm_four {K : Set D} {f : D → F}
    (hK : IsCompact K) (hf : ∀ q ∈ K, ContDiffAt ℝ 4 f q)
    {q : D} (hq : q ∈ K) {j : ℕ} (hj : j + 1 ≤ 4) :
    ‖iteratedFDeriv ℝ j (fderiv ℝ f) q‖ ≤ cNorm K 4 f := by
  rw [norm_iteratedFDeriv_fderiv]
  exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hf hq hj

/-- The two differentiations in the quotient's physical gradient leave two
further joint derivatives in the `C⁴` budget of
`app:ch_seed:prop:seed-phase-charts`. -/
theorem norm_phaseHessian_jet_le_cNorm_four {K : Set D} {f : D → F}
    (hK : IsCompact K) (hf : ∀ q ∈ K, ContDiffAt ℝ 4 f q)
    {q : D} (hq : q ∈ K) {j : ℕ} (hj : j + 2 ≤ 4) :
    ‖iteratedFDeriv ℝ j (fderiv ℝ (fderiv ℝ f)) q‖ ≤ cNorm K 4 f := by
  rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
  exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hf hq hj

/-- Mixed physical/covector evaluations are controlled by the original phase
seminorm, for the actual integrand in `app:ch_seed:eq:seed-quotient-integral`.
The directions are arbitrary, so none of the mixed derivatives is discarded. -/
theorem norm_phaseHessian_apply_le_cNorm_four {K : Set D} {f : D → F}
    (hK : IsCompact K) (hf : ∀ q ∈ K, ContDiffAt ℝ 4 f q)
    {q : D} (hq : q ∈ K) (v w : D) :
    ‖fderiv ℝ (fderiv ℝ f) q v w‖ ≤ cNorm K 4 f * ‖v‖ * ‖w‖ := by
  have hb : ‖fderiv ℝ (fderiv ℝ f) q‖ ≤ cNorm K 4 f := by
    simpa only [norm_iteratedFDeriv_zero] using
      norm_phaseHessian_jet_le_cNorm_four hK hf hq (j := 0) (by norm_num)
  exact ((fderiv ℝ (fderiv ℝ f) q v).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right
      (((fderiv ℝ (fderiv ℝ f) q).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hb (norm_nonneg v))) (norm_nonneg w))

end JanetCartan.FullPhaseCharts.Comparison
