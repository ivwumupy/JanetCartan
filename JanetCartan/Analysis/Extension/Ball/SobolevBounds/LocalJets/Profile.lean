module

public import JanetCartan.Analysis.Extension.Ball.ContinuousBounds

/-!
# Pointwise input-jet bounds for the fixed collar profile

The local estimate underlying `app:ch_regular_base:eq:extension-collar-l2`
uses only jets at the actual sampling point. Compactness is used only for the
fixed cutoff and geometry, so the constant is independent of the input function.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.BallExtension.Parameters

private theorem exists_compact_geometry_jet_bound
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {s K : Set X} (hK : IsCompact K) (hKs : K ⊆ s) (hs : UniqueDiffOn ℝ s)
    {g : X → Y} (hg : ContDiffOn ℝ ∞ g s) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i ≤ m, ∀ z ∈ K,
      ‖iteratedFDerivWithin ℝ i g s z‖ ≤ B := by
  have hb (i : ℕ) : ∃ B : ℝ, ∀ z ∈ K, ‖iteratedFDerivWithin ℝ i g s z‖ ≤ B :=
    hK.exists_bound_of_continuousOn
      ((hg.continuousOn_iteratedFDerivWithin (by simp) hs).mono hKs)
  choose B hB using hb
  refine ⟨1 + ∑ i ∈ Finset.range (m + 1), max 0 (B i), ?_, ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ ↦ le_max_left _ _))
  · intro i hi z hz
    have hsum := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.range (m + 1)) ↦ le_max_left 0 (B j))
      (Finset.mem_range.mpr (show i < m + 1 by omega))
    linarith [hB i z hz, le_max_right 0 (B i)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (p : JanetCartan.BallExtension.Parameters E)

/-- The fixed profile in `app:ch_regular_base:eq:extension-collar-l2` is bounded
linearly in the input jets at its sampling point, with a constant independent of `f`. -/
theorem exists_collarProfile_local_jet_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) →
      ∀ i ≤ m, ∀ z ∈ Icc 0 p.width ×ˢ p.compactExteriorCollar,
        ‖iteratedFDerivWithin ℝ i (p.collarProfile f) p.collarProfileDomain z‖ ≤
          C * ∑ j ∈ Finset.range (m + 1),
            ‖iteratedFDerivWithin ℝ j f (closedBall p.center p.radius) (p.collarSample z)‖ := by
  let K := Icc 0 p.width ×ˢ p.compactExteriorCollar
  have hK : IsCompact K := isCompact_Icc.prod p.isCompact_compactExteriorCollar
  have hcut : ContDiffOn ℝ ∞ (fun z : ℝ × E ↦ p.cutoff z.1) p.collarProfileDomain :=
    p.cutoff.contDiff.comp_contDiffOn contDiffOn_fst
  obtain ⟨A, hA, hcutB⟩ := exists_compact_geometry_jet_bound hK p.compactCollar_subset_profileDomain
    p.uniqueDiffOn_collarProfileDomain hcut m
  obtain ⟨B, hB, hsampleB⟩ := exists_compact_geometry_jet_bound hK p.compactCollar_subset_profileDomain
    p.uniqueDiffOn_collarProfileDomain p.contDiffOn_collarSample m
  let C : ℕ → ℝ := fun i ↦ ∑ j ∈ Finset.range (i + 1),
    (i.choose j : ℝ) * A * ((i - j).factorial : ℝ) * B ^ (i - j)
  have hC (i : ℕ) : 0 ≤ C i := by dsimp [C]; positivity
  refine ⟨∑ i ∈ Finset.range (m + 1), C i, Finset.sum_nonneg (fun i _ ↦ hC i), ?_⟩
  intro f hf i hi z hz
  let M : ℝ := ∑ j ∈ Finset.range (m + 1),
    ‖iteratedFDerivWithin ℝ j f (closedBall p.center p.radius) (p.collarSample z)‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hjet (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDerivWithin ℝ j f (closedBall p.center p.radius) (p.collarSample z)‖ ≤ M :=
    Finset.single_le_sum (s := Finset.range (m + 1)) (a := j)
      (f := fun l ↦ ‖iteratedFDerivWithin ℝ l f (closedBall p.center p.radius)
        (p.collarSample z)‖)
      (fun _ _ ↦ norm_nonneg _) (Finset.mem_range.mpr (by omega))
  have hzD := p.compactCollar_subset_profileDomain hz
  have hcomp (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDerivWithin ℝ j (f ∘ p.collarSample) p.collarProfileDomain z‖ ≤
        (j.factorial : ℝ) * M * B ^ j := by
    apply norm_iteratedFDerivWithin_comp_le hf p.contDiffOn_collarSample (by simp)
      p.uniqueDiffOn_closedBall p.uniqueDiffOn_collarProfileDomain
      (fun _ hy ↦ p.collarSample_mem_closedBall hy) hzD
    · intro l hl
      exact hjet l (hl.trans hj)
    · intro l hl hlm
      exact (hsampleB l (hlm.trans hj) z hz).trans (le_self_pow₀ hB (by omega))
  calc
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
        ‖iteratedFDerivWithin ℝ j (fun z : ℝ × E ↦ p.cutoff z.1) p.collarProfileDomain z‖ *
        ‖iteratedFDerivWithin ℝ (i - j) (f ∘ p.collarSample) p.collarProfileDomain z‖ :=
      norm_iteratedFDerivWithin_mul_le hcut
        (hf.comp p.contDiffOn_collarSample (fun _ hy ↦ p.collarSample_mem_closedBall hy))
        p.uniqueDiffOn_collarProfileDomain hzD (by simp)
    _ ≤ ∑ j ∈ Finset.range (i + 1),
        (i.choose j : ℝ) * A * (((i - j).factorial : ℝ) * M * B ^ (i - j)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hcutB j (by have := Finset.mem_range.mp hj; omega) z hz)
          (by positivity)) (hcomp (i - j) (by omega)) (norm_nonneg _)
          (mul_nonneg (by positivity) (by linarith))
    _ = C i * M := by dsimp [C]; rw [Finset.sum_mul]; congr 1; ext j; ring
    _ ≤ (∑ l ∈ Finset.range (m + 1), C l) * M :=
      mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun l _ ↦ hC l) (Finset.mem_range.mpr (by omega))) hM

end JanetCartan.BallExtension.Parameters
