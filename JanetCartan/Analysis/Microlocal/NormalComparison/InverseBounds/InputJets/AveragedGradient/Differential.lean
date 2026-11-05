module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.Base

/-! # Spatial differential along the two-position segment

The explicit derivative budget for `app:ch_osc:setup:osc-normal`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.NormalComparison

/-- Segment substitution retaining both independent physical positions
(`app:ch_osc:setup:osc-normal`). -/
def averagedGradientSegmentInput (n : ℕ) (t : ℝ) :
    (Euclidean n × (Euclidean n × Euclidean n)) →L[ℝ] (Euclidean n × Euclidean n) :=
  let x := ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n × Euclidean n)
  let y := (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)).comp
    (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n × Euclidean n))
  let u := (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n)).comp
    (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n × Euclidean n))
  (y + t • (x - y)).prod u

/-- Formula for the segment substitution (`app:ch_osc:setup:osc-normal`). -/
@[simp] theorem averagedGradientSegmentInput_apply (n : ℕ) (t : ℝ)
    (q : Euclidean n × (Euclidean n × Euclidean n)) :
    averagedGradientSegmentInput n t q = (q.2.1 + t • (q.1 - q.2.1), q.2.2) := rfl

/-- A dimension-independent bound for the segment substitution
(`app:ch_osc:prop:osc-normal`). -/
theorem norm_averagedGradientSegmentInput_le (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖averagedGradientSegmentInput n t‖ ≤ 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro q
  change max ‖q.2.1 + t • (q.1 - q.2.1)‖ ‖q.2.2‖ ≤ 3 * ‖q‖
  have hx := norm_fst_le q
  have hy := (norm_fst_le q.2).trans (norm_snd_le q)
  have hu := (norm_snd_le q.2).trans (norm_snd_le q)
  apply max_le
  · calc
      _ ≤ ‖q.2.1‖ + ‖t • (q.1 - q.2.1)‖ := norm_add_le _ _
      _ = ‖q.2.1‖ + t * ‖q.1 - q.2.1‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ ‖q.2.1‖ + 1 * (‖q.1‖ + ‖q.2.1‖) := by
        exact add_le_add le_rfl
          (mul_le_mul ht.2 (norm_sub_le q.1 q.2.1) (norm_nonneg (q.1 - q.2.1)) zero_le_one)
      _ ≤ 3 * ‖q‖ := by linarith
  · nlinarith [norm_nonneg q]

/-- Restriction of the full spatial differential to the physical direction
(`app:ch_osc:setup:osc-normal`). -/
def phaseDifferentialRestriction (n : ℕ) :
    ((Euclidean n × Euclidean n) →L[ℝ] ℝ) →L[ℝ] (Euclidean n →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (Euclidean n) (Euclidean n × Euclidean n) ℝ).flip
    (ContinuousLinearMap.inl ℝ (Euclidean n) (Euclidean n))

/-- Restriction to the physical direction is a contraction
(`app:ch_osc:prop:osc-normal`). -/
theorem norm_phaseDifferentialRestriction_le (n : ℕ) :
    ‖phaseDifferentialRestriction n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simpa [phaseDifferentialRestriction] using L.le_opNorm (v, 0)

/-- The restricted full differential equals the actual partial differential
(`app:ch_osc:setup:osc-normal`). -/
theorem phaseDifferentialRestriction_fderiv {n : ℕ}
    {φ : Euclidean n → Euclidean n → ℝ} {z : Euclidean n × Euclidean n}
    (hφ : DifferentiableAt ℝ (Function.uncurry φ) z) :
    phaseDifferentialRestriction n (fderiv ℝ (Function.uncurry φ) z) =
      fderiv ℝ (fun x ↦ φ x z.2) z.1 := by
  exact ((hφ.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)).fderiv).symm

/-- The full spatial differential loses exactly one derivative; restricting
to physical directions costs at most one (`app:ch_osc:prop:osc-normal`). -/
theorem norm_iteratedFDeriv_phaseDifferential_le {n : ℕ}
    {φ : Euclidean n → Euclidean n → ℝ} {z : Euclidean n × Euclidean n}
    (hφ : ContDiffAt ℝ ∞ (Function.uncurry φ) z) (k : ℕ) :
    ‖iteratedFDeriv ℝ k
      (fun w ↦ phaseDifferentialRestriction n (fderiv ℝ (Function.uncurry φ) w)) z‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) (Function.uncurry φ) z‖ := by
  calc
    _ ≤ ‖phaseDifferentialRestriction n‖ *
        ‖iteratedFDeriv ℝ k (fderiv ℝ (Function.uncurry φ)) z‖ :=
      (phaseDifferentialRestriction n).norm_iteratedFDeriv_comp_left
        (hφ.fderiv_right (m := ∞) (by simp)) (by simp)
    _ ≤ 1 * ‖iteratedFDeriv ℝ k (fderiv ℝ (Function.uncurry φ)) z‖ := by
      gcongr
      exact norm_phaseDifferentialRestriction_le n
    _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

/-- Explicit averaged-gradient jet budget, quantified before the phase family
(`app:ch_osc:prop:osc-normal`). -/
def averagedGradientJetBound (C : ℕ → ℝ) (k : ℕ) : ℝ := 3 ^ k * |C (k + 1)|

/-- Nonnegativity of the averaged-gradient budget (`app:ch_osc:prop:osc-normal`). -/
theorem averagedGradientJetBound_nonneg (C : ℕ → ℝ) (k : ℕ) :
    0 ≤ averagedGradientJetBound C k := by unfold averagedGradientJetBound; positivity

end JanetCartan.NormalComparison
