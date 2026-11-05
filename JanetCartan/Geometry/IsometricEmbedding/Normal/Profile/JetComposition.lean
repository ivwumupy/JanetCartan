module

public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Analysis.ContDiff.Norm.Composition

/-!
# Estimates for coefficients of the first jet

The derivative shift and chain-rule steps for `app:ch_background:eq:bg-frame-tame`
and `app:ch_waves:eq:joint-tame`. The polynomial estimate is unconditional.
The general compact-domain one-high estimate retains scalar interpolation as an
input. The closed-ball variant discharges it using the proved interpolation API.
Neither result uses the unfinished interpolation declaration.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.GeometricProfile

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `app:ch_background:eq:bg-frame-tame`: taking the first jet costs one derivative
in the actual sum-of-suprema seminorm. This inequality needs no regularity assumption. -/
theorem cNorm_fderiv_le (s : Set E) (r : ℕ) (f : E → F) :
    cNorm s r (fderiv ℝ f) ≤ cNorm s (r + 1) f := by
  unfold cNorm
  simp_rw [norm_iteratedFDeriv_fderiv]
  conv_rhs => rw [Finset.sum_range_succ']
  exact le_add_of_nonneg_right (sSup_norm_iteratedFDeriv_nonneg s 0 f)

/-- `app:ch_background:eq:bg-frame-tame`: the polynomial chain-rule estimate for a
coefficient of the first jet, smooth near a fixed compact range. -/
theorem cNorm_firstJet_comp_le_polynomial
    {s : Set E} {t : Set (E →L[ℝ] F)} (hs : IsCompact s) (ht : IsCompact t)
    {r : ℕ} {g : (E →L[ℝ] F) → G} (hg : ∀ L ∈ t, ContDiffAt ℝ r g L)
    {f : E → F} (hf : ContDiff ℝ (r + 1) f) (hft : Set.MapsTo (fderiv ℝ f) s t) :
    cNorm s r (g ∘ fderiv ℝ f) ≤
      compositionMultiplicity r * cNorm t r g * (1 + cNorm s (r + 1) f) ^ r := by
  have hdf : ContDiff ℝ r (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h := cNorm_comp_le_polynomial (fun _ _ ↦ hdf.contDiffAt)
    (fun x hx ↦ hg _ (hft hx)) (fun j hj ↦ bddAbove_norm_iteratedFDeriv hs hdf hj)
    (cNorm_nonneg t r g)
    (fun j hj x hx ↦ norm_iteratedFDeriv_le_cNorm_of_contDiffAt ht hg (hft hx) hj)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)) (cNorm_nonneg t r g))
  exact pow_le_pow_left₀ (by linarith [cNorm_nonneg s r (fderiv ℝ f)])
    (add_le_add (le_refl 1) (cNorm_fderiv_le s r f)) r

/-- `app:ch_waves:eq:joint-tame`: a coefficient of the first jet has one high map norm,
conditional on the displayed scalar interpolation estimates. The constant is chosen before the
map. Only compact-range coefficient smoothness and the fixed low bound are used. -/
theorem exists_cNorm_firstJet_comp_le_of_interpolation
    {s : Set E} {t : Set (E →L[ℝ] F)} (hs : IsCompact s) (ht : IsCompact t)
    {r k : ℕ} (hk : 0 < k) (hrk : r ≤ k) {g : (E →L[ℝ] F) → G}
    (hg : ∀ L ∈ t, ContDiffAt ℝ r g L) {M : ℝ} (hM : 0 ≤ M)
    (hinterp : ∀ j, 0 < j → j < k → ∃ C : ℝ, 0 < C ∧
      ∀ u : E → (E →L[ℝ] F), ContDiff ℝ ∞ u →
        cNorm s j u ≤ C * (cNorm s 0 u) ^ (1 - (j : ℝ) / k) *
          (cNorm s k u) ^ ((j : ℝ) / k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E → F, ContDiff ℝ ∞ f →
      Set.MapsTo (fderiv ℝ f) s t → cNorm s 1 f ≤ M →
        cNorm s r (g ∘ fderiv ℝ f) ≤ C * (1 + cNorm s (k + 1) f) := by
  obtain ⟨A, hA, hAI⟩ := CompositionBounds.exists_uniform_interpolation_constant s k hinterp
  let D := compositionMultiplicity r * cNorm t r g * (A * (1 + M)) ^ r
  have hD : 0 ≤ D := by
    dsimp [D, compositionMultiplicity]
    exact mul_nonneg (mul_nonneg (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _))
      (cNorm_nonneg t r g)) (pow_nonneg (mul_nonneg (zero_le_one.trans hA) (by linarith)) _)
  refine ⟨1 + D, by positivity, ?_⟩
  intro f hf hft hfM
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h := cNorm_comp_le_tame_of_interpolation hs hk hrk
    (contDiff_infty.mp hdf k) (fun x hx ↦ hg _ (hft hx)) hA
    (cNorm_nonneg t r g) ((cNorm_fderiv_le s 0 f).trans hfM) (hAI _ hdf)
    (fun j hj x hx ↦ norm_iteratedFDeriv_le_cNorm_of_contDiffAt ht hg (hft hx) hj)
  exact h.trans ((mul_le_mul_of_nonneg_left
    (add_le_add (le_refl 1) (cNorm_fderiv_le s k f)) hD).trans
    (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith : D ≤ 1 + D)
      (by linarith [cNorm_nonneg s (k + 1) f])))

/-- `app:ch_background:eq:bg-frame-tame`: on positive-radius closed balls,
proved interpolation discharges the scalar input and the compact first-jet
range supplies the low norm. The exact derivative loss is one. -/
theorem exists_cNorm_firstJet_comp_le_closedBall [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) {t : Set (E →L[ℝ] F)} (ht : IsCompact t)
    {r : ℕ} {g : (E →L[ℝ] F) → G} (hg : ∀ J ∈ t, ContDiffAt ℝ r g J) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E → F, ContDiff ℝ ∞ f →
      Set.MapsTo (fderiv ℝ f) (Metric.closedBall x ρ) t →
        cNorm (Metric.closedBall x ρ) r (g ∘ fderiv ℝ f) ≤
          C * (1 + cNorm (Metric.closedBall x ρ) (r + 1) f) := by
  obtain ⟨C, hC, hbound⟩ := exists_cNorm_comp_le_tame_closedBall_of_compact_range
    x hρ ht (le_refl r) hg
  refine ⟨C, hC, fun f hf hft ↦ ?_⟩
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact (hbound _ hd hft).trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl 1) (cNorm_fderiv_le _ r f)) hC.le)

end JanetCartan.GeometricProfile
