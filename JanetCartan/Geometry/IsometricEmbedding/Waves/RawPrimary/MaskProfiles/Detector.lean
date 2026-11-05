module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.MaskProfiles.Profiles

/-!
# Regularity and boundedness of the original detector/high-pass product

The given high-pass vanishes through radius one and is one above radius two.
Its multiplication with the degree-zero angular detector is smooth even at
zero, and bounded globally. These are the unnormalized mask inputs of
`CanonicalSlice.exists_canonical_rawSliceSobolev`
(`app:ch_background:defn:bg-row`, `app:ch_waves:eq:B-bounds`).
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.RawPrimary.MaskProfiles

variable {n : ℕ}
local notation "E" => Euclidean (n - 1)

/-- The original high-pass removes the angular singularity at the origin
(`app:ch_background:defn:bg-row`). -/
theorem contDiff_detectorMask (a : E → ℂ) (H : E → ℝ)
    (ha : ∀ θ : E, θ ≠ 0 → ContDiffAt ℝ ∞ a θ)
    (hH : ContDiff ℝ ∞ H) (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0) :
    ContDiff ℝ ∞ (detectorMask a H) := by
  rw [contDiff_iff_contDiffAt]
  intro η
  by_cases hη : η = 0
  · subst η
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1)] with η hη
    simp [detectorMask, hH₀ η (mem_ball_zero_iff.mp hη).le]
  · exact (ha η hη).mul ((Complex.ofRealCLM.contDiff.comp hH).contDiffAt)

/-- Compactness of the unit sphere bounds a smooth degree-zero angular
detector globally away from zero, without parity or a prescribed seminorm
(`app:ch_waves:eq:B-bounds`). -/
theorem exists_bound_angularDetector (a : E → ℂ)
    (ha : ∀ θ : E, θ ≠ 0 → ContDiffAt ℝ ∞ a θ)
    (hah : ∀ r : ℝ, 0 < r → ∀ θ, a (r • θ) = a θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ, θ ≠ 0 → ‖a θ‖ ≤ C := by
  have hc : ContinuousOn a (sphere (0 : E) 1) := by
    intro θ hθ
    apply (ha θ ?_).continuousAt.continuousWithinAt
    intro he
    subst θ
    simp at hθ
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn hc
  refine ⟨max 0 C, le_max_left _ _, fun θ hθ ↦ ?_⟩
  have hnorm : ‖(‖θ‖⁻¹ : ℝ) • θ‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hθ)]
  have hb := hC ((‖θ‖⁻¹ : ℝ) • θ) (mem_sphere_zero_iff_norm.mpr hnorm)
  rw [hah _ (inv_pos.mpr (norm_pos_iff.mpr hθ))] at hb
  exact hb.trans (le_max_right _ _)

/-- Smoothness and the exterior plateau bound the fixed high-pass globally
(`app:ch_background:defn:bg-row`). -/
theorem exists_bound_highPass (H : E → ℝ) (hH : ContDiff ℝ ∞ H)
    (hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η, ‖H η‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) 2).exists_bound_of_continuousOn
    hH.continuous.continuousOn
  refine ⟨max 1 C, (by linarith [le_max_left (1 : ℝ) C]), fun η ↦ ?_⟩
  by_cases hη : ‖η‖ ≤ 2
  · exact (hC η (mem_closedBall_zero_iff.mpr hη)).trans (le_max_right _ _)
  · rw [hH₁ η (le_of_not_ge hη), norm_one]
    exact le_max_left _ _

/-- The original complex detector/high-pass is globally bounded. Its bound
is derived from primitive angular smoothness and homogeneity, and the actual
high-pass properties (`app:ch_waves:eq:B-bounds`). -/
theorem exists_bound_detectorMask (a : E → ℂ) (H : E → ℝ)
    (ha : ∀ θ : E, θ ≠ 0 → ContDiffAt ℝ ∞ a θ)
    (hah : ∀ r : ℝ, 0 < r → ∀ θ, a (r • θ) = a θ)
    (hH : ContDiff ℝ ∞ H) (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0)
    (hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η, ‖detectorMask a H η‖ ≤ C := by
  obtain ⟨A, hA, haBound⟩ := exists_bound_angularDetector a ha hah
  obtain ⟨B, hB, hHBound⟩ := exists_bound_highPass H hH hH₁
  refine ⟨A * B, mul_nonneg hA hB, fun η ↦ ?_⟩
  by_cases hη : η = 0
  · subst η
    simpa [detectorMask, hH₀ 0 (by simp)] using mul_nonneg hA hB
  · simpa only [detectorMask, norm_mul, Complex.norm_real] using
      mul_le_mul (haBound η hη) (hHBound η) (norm_nonneg _) hA

end JanetCartan.RawPrimary.MaskProfiles
