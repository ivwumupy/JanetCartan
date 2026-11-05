module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.CorrectedSamplingMean.Literal

/-!
# Covector-only pullback at a fixed physical rate

The existing normalized substitution is used after dropping its first output
coordinate. Thus its epsilon jets differentiate only the shifted covector,
not the physical inverse frequency of the response. The original normalized
mask profiles give constants uniform in the band label.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedMean
open ActualCarriers FrozenMenu CurrentFullPhase
open FullNormalGeometry.PhaseJets MeasuredAmplitude

/-- Pullback jets for a coefficient whose physical rate is fixed. This
specializes the existing pullback calculus to a function independent of its
first argument, and therefore assumes no regularity at physical rate zero.
Consumer: the corrected amplitude fields in `UniformNormalData`
(`app:ch_waves:setup:oscillatory`, `app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_fixedRatePullback_budgets
    {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    (M : ℝ) {e : ℝ} (he : e ≤ 1)
    {S : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))}
    (hS : IsCompact S) (hSM : S ⊆ tripleDomain T M)
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    (hhigh : ContDiff ℝ ∞ highPass) (hhigh₁ : ∀ η, 2 ≤ ‖η‖ → highPass η = 1)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ D : ℕ → ℝ, (∀ j, 0 ≤ D j) ∧
      ∀ (f : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) →
        EuclideanSpace ℂ (Fin (m + 1))), ContDiff ℝ ∞ f →
      ∀ (L : ℝ) (rpar : ℕ), 1 ≤ L →
      (∀ w j, ‖iteratedFDeriv ℝ j f w‖ ≤ A j * L ^ (j - rpar)) →
      ∀ j,
        let g := normalizedMeasuredPullback T ψ angular highPass (fun q ↦ f q.2) j
        ContDiffOn ℝ ∞ g (univ ×ˢ tripleDomain T M) ∧
          ∀ q ∈ Icc (-e) e ×ˢ S, ∀ k, ‖iteratedFDeriv ℝ k g q‖ ≤ D k * L ^ (k - rpar) := by
  obtain ⟨D, hD, hbound⟩ := exists_normalizedMeasuredPullback_budgets T hP M he hS hSM
    ψ hψ angular highPass ha hah hhigh hhigh₁ A hA
  refine ⟨D, hD, ?_⟩
  intro f hf L rpar hL hfjet j
  apply hbound (fun q ↦ f q.2) (hf.comp contDiff_snd) L rpar hL _ j
  intro τ _ w k
  let pr := ContinuousLinearMap.snd ℝ ℝ
    (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  exact ((NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le pr
    (f := f) (x := (τ, w)) isOpen_univ hf.contDiffOn (mem_univ _) k).trans
      (mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le _ _ _)))).trans (hfjet w k)

end JanetCartan.Sampling.CorrectedMean
