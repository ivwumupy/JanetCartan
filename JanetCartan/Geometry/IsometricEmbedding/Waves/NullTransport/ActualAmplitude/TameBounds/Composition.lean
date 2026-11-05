module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.LocalNorms
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition

/-!
# Composition and products for the null amplitude

The characteristic coefficient and footpoint pullback in
`app:ch_waves:eq:joint-tame` compose two varying maps. We specialize the
existing additive composition and product estimates to every natural order,
including zero and one, with one fixed reserve two. Exponentiation uses only
a fixed zeroth-order budget and has no derivative loss.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.NullTransport.AmplitudeTame

open FullPhaseCharts.InverseEstimates

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `app:ch_waves:eq:joint-tame`: the additive composition bound at every
order, with fixed reserve two and fixed `C¹` budgets. The actual potential
along the forward flow and the final footpoint pullback consume this estimate.
Both maps are quantified after the constant. -/
theorem exists_cNorm_comp_le_joint_tame_closedBall
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (a : E) (b : F) {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    (ha : closedBall a ρ ⊆ U) (hb : closedBall b σ ⊆ V)
    (m : ℕ) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : E → F) (g : F → G),
      ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g V →
      MapsTo f (closedBall a ρ) (closedBall b σ) →
      cNorm (closedBall a ρ) 1 f ≤ M → cNorm (closedBall b σ) 1 g ≤ N →
      cNorm (closedBall a ρ) m (g ∘ f) ≤
        C * (1 + cNorm (closedBall a ρ) (m + 2) f +
          cNorm (closedBall b σ) (m + 2) g) := by
  obtain ⟨C, hC, hc⟩ := exists_cNorm_comp_le_additive_oneHigh (F := G)
    a b hρ hσ hU hV ha hb (show 2 ≤ m + 2 by omega) hM hN
  exact ⟨C, hC, fun f g hf hg hmap hfM hgN ↦
    (cNorm_mono_order (show m ≤ m + 2 by omega)).trans (hc f g hf hg hmap hfM hgN)⟩

/-- `app:ch_waves:eq:joint-tame`: scalar multiplication retains an additive
high norm at every order. It is applied first to the initial scalar and the
flow exponential, then to the scalar amplitude and the actual nullvector. -/
theorem exists_cNorm_smul_le_joint_tame_closedBall
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (a : E) {ρ : ℝ} (hρ : 0 < ρ) {U : Set E} (hU : IsOpen U)
    (ha : closedBall a ρ ⊆ U) (m : ℕ) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : E → ℝ) (g : E → F),
      ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      cNorm (closedBall a ρ) 1 f ≤ M → cNorm (closedBall a ρ) 1 g ≤ N →
      cNorm (closedBall a ρ) m (fun x ↦ f x • g x) ≤
        C * (1 + cNorm (closedBall a ρ) (m + 2) f +
          cNorm (closedBall a ρ) (m + 2) g) := by
  obtain ⟨C, hC, hc⟩ := exists_cNorm_bilinear_le_additive_oneHigh
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)
    a hρ hU ha (show 2 ≤ m + 2 by omega) hM hN
  exact ⟨C, hC, fun f g hf hg hfM hgN ↦
    (cNorm_mono_order (show m ≤ m + 2 by omega)).trans (hc f g hf hg hfM hgN)⟩

/-- `app:ch_waves:eq:joint-tame`: the exponential of the negative time
integral has a one-high bound from a fixed value budget. The time-integral
estimate must supply this budget; it is not an assumption on the exponential. -/
theorem exists_cNorm_exp_neg_le_joint_tame_closedBall
    [FiniteDimensional ℝ E] (a : E) {ρ : ℝ} (hρ : 0 < ρ)
    (m : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set E), IsOpen U → closedBall a ρ ⊆ U →
      ∀ f : E → ℝ, ContDiffOn ℝ ∞ f U → cNorm (closedBall a ρ) 0 f ≤ M →
        cNorm (closedBall a ρ) m (fun x ↦ Real.exp (-f x)) ≤
          C * (1 + cNorm (closedBall a ρ) m f) := by
  obtain ⟨C, hC, hc⟩ := ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn
    a hρ (isCompact_closedBall (0 : ℝ) M) (le_refl m)
    (g := fun t : ℝ ↦ Real.exp (-t)) (fun _ _ ↦
      (Real.contDiff_exp.comp contDiff_neg).contDiffAt)
  refine ⟨C, hC, ?_⟩
  intro U hU hball f hf hM
  apply hc U hU hball f hf
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  apply le_trans _ hM
  simpa only [norm_iteratedFDeriv_zero] using
    norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
      (fun y hy ↦ (hf.contDiffAt (hU.mem_nhds (hball hy))).of_le
        (show (0 : ℕ∞ω) ≤ ∞ by simp)) hx (le_refl 0)

end JanetCartan.NullTransport.AmplitudeTame
