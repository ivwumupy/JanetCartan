module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingRealization
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RefinedKernels

/-!
# Removing the sampling color masks by positivity

This is the first step in the proof following
`app:ch_waves:eq:sampling-operator-bounds`. The literal finite colored masks
lie in `[0,1]`, by the window support and separation of equal-color blocks.
The full-output normal is therefore dominated by the sum of the unmasked
color normals. No color-mask derivative or trace bound enters this reduction.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators

namespace JanetCartan.Sampling.MeanNormalBound
open SeparatedSampling BackgroundQuadrature Realization SamplingKernelBounds

/-- At any point at most one block of a fixed color has nonzero weight.
This is the support fact behind `0 ≤ m_c ≤ 1` in the mask-free proof of
`app:ch_waves:eq:sampling-operator-bounds`. -/
theorem eq_of_same_color_of_blockWeight_ne_zero
    {p : ℕ} {w : ℝ → ℝ} {W h : ℝ} (hw : WindowBounds p w W)
    {q r : Lattice} {z : Point} (hc : color p q = color p r)
    (hq : blockWeight w h q z ≠ 0) (hr : blockWeight w h r z ≠ 0) : q = r := by
  by_contra hqr
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hqr
  have hg := color_coordinate_gap hc hi
  have hq' := hw.support _ ((Finset.prod_ne_zero_iff.mp hq) i (Finset.mem_univ i))
  have hr' := hw.support _ ((Finset.prod_ne_zero_iff.mp hr) i (Finset.mem_univ i))
  have ht : |(q i : ℝ) - (r i : ℝ)| ≤
      |z i / h - (q i : ℝ)| + |z i / h - (r i : ℝ)| := by
    calc
      _ = |-(z i / h - (q i : ℝ)) + (z i / h - (r i : ℝ))| := by congr 1; ring
      _ ≤ _ := by simpa only [abs_neg] using
        abs_add_le (-(z i / h - (q i : ℝ))) (z i / h - (r i : ℝ))
  dsimp [windowRadius] at hq' hr'
  linarith

/-- The original finite colored mask lies in `[0,1]`, uniformly in the mesh,
enumeration and color (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem coloredBlockMask_bounds {p : ℕ} {w : ℝ → ℝ}
    (hw : WindowBounds p w 1) (s : Finset Lattice) (h : ℝ)
    (c : Fin 3 → Fin (p + 1)) (z : Point) :
    0 ≤ coloredBlockMask p s w h c z ∧ coloredBlockMask p s w h c z ≤ 1 := by
  classical
  have hnonneg (q : Lattice) : 0 ≤ blockWeight w h q z :=
    Finset.prod_nonneg fun i _ ↦ hw.nonneg _
  refine ⟨Finset.sum_nonneg (fun q _ ↦ hnonneg q), ?_⟩
  by_cases hex : ∃ q ∈ s.filter (fun q ↦ color p q = c), blockWeight w h q z ≠ 0
  · obtain ⟨q, hq, hqne⟩ := hex
    have he : coloredBlockMask p s w h c z = blockWeight w h q z := by
      apply Finset.sum_eq_single q
      · intro r hr hrq
        by_contra hrne
        exact hrq (eq_of_same_color_of_blockWeight_ne_zero hw
          ((Finset.mem_filter.mp hr).2.trans (Finset.mem_filter.mp hq).2.symm) hrne hqne)
      · exact fun h ↦ (h hq).elim
    rw [he]
    exact Finset.prod_le_one₀ (fun i _ ↦ hw.nonneg _) (fun i _ ↦ hw.le_bound _)
  · have hz : coloredBlockMask p s w h c z = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      by_contra hne
      exact hex ⟨q, hq, hne⟩
    rw [hz]
    exact zero_le_one

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- All Bochner integrability needed for mask removal follows from the fixed
compact measurement weight and operator continuity
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_patch_normal {ψ : Point → ℝ} {B P : ℝ}
    (hψ : PatchBounds ψ B P) (hψc : Continuous ψ)
    (T : Point → E →L[ℂ] H) (hT : Continuous T) :
    Integrable (fun z ↦ ψ z • atomNormal (T z)) := by
  have hs : HasCompactSupport ψ := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Point) B)
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hψ.radius_nonneg).mpr
      (fun i ↦ by simpa only [Real.norm_eq_abs] using hψ.support z hz i)
  exact (hψc.smul (hT.clm_comp (ContinuousLinearMap.adjoint.continuous.comp hT))).integrable_of_hasCompactSupport
    hs.smul_right

/-- Remove the literal color masks in operator order before applying any
physical derivative estimate (`app:ch_waves:eq:sampling-operator-bounds`).
All integrals use the original sampling Lebesgue measure. -/
theorem patchMeanNormal_le_unmasked {p : ℕ} {B P h : ℝ}
    {ψ : Point → ℝ} {w : ℝ → ℝ} (hw : WindowBounds p w 1)
    (hψ : PatchBounds ψ B P) (hψc : Continuous ψ) (hwc : Continuous w) (hh : h ≠ 0)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) :
    patchMeanNormal p B ψ w h T ≤ ∑ c, ∫ z : Point, ψ z • atomNormal (T c z) := by
  classical
  rw [patchMeanNormal_eq_colored hw hψc hwc hh T hT]
  apply Finset.sum_le_sum
  intro c _
  have hi : Integrable (fun z ↦
      coloredBlockMask p (integerCube (blockCutoff p B h)) w h c z •
        (ψ z • atomNormal (T c z))) := by
    simp only [coloredBlockMask, Finset.sum_smul]
    exact integrable_finsetSum _ (fun q _ ↦ integrable_blockWeight_smul hw hwc hh q
      (hψc.smul ((hT c).clm_comp (ContinuousLinearMap.adjoint.continuous.comp (hT c)))))
  apply integral_mono hi (integrable_patch_normal hψ hψc (T c) (hT c))
  intro z
  simpa only [one_smul] using smul_le_smul_of_nonneg_right
    (coloredBlockMask_bounds hw (integerCube (blockCutoff p B h)) h c z).2
    (smul_nonneg (hψ.nonneg z) (atomNormal_nonneg (T c z)))

/-- Norm domination for the complete finite chart family. The bound contains
no mesh, band-count, or color-mask derivative loss
(`app:ch_waves:eq:sampling-operator-bounds`). The unmasked estimate itself is
the separate finite-overlap analytic obligation. -/
theorem norm_sum_patchMeanNormal_le_unmasked {A : Type*} [Fintype A]
    {p : ℕ} {B h : ℝ} {P : A → ℝ} {ψ : A → Point → ℝ} {w : ℝ → ℝ}
    (hw : WindowBounds p w 1) (hψ : ∀ a, PatchBounds (ψ a) B (P a))
    (hψc : ∀ a, Continuous (ψ a)) (hwc : Continuous w) (hh : h ≠ 0)
    (T : A → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ a c, Continuous (T a c)) :
    ‖∑ a, patchMeanNormal p B (ψ a) w h (T a)‖ ≤
      ‖∑ a, ∑ c, ∫ z : Point, ψ a z • atomNormal (T a c z)‖ := by
  apply CStarAlgebra.norm_le_norm_of_le_of_nonneg
  · exact Finset.sum_le_sum fun a _ ↦
      patchMeanNormal_le_unmasked hw (hψ a) (hψc a) hwc hh (T a) (hT a)
  · exact Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun q _ ↦
      integral_nonneg fun z ↦ smul_nonneg
        (mul_nonneg ((hψ a).nonneg z) (Finset.prod_nonneg fun i _ ↦ hw.nonneg _))
        (atomNormal_nonneg _)

/-- Mask removal on exactly the largest `refinedKernelPrefix` consumed by
`Sampling.exists_threshold_refinedKernelPrefix_realization`. Both sharp
Hilbert components remain grouped under the same original smooth band;
this lemma does not estimate their amplitudes
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_refinedKernelPrefix_mean_le_unmasked {A : Type*} [Fintype A]
    {n J p : ℕ}
    (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    {B h : ℝ} {P : A → ℝ} {ψ : A → Point → ℝ} {w : ℝ → ℝ}
    (hw : WindowBounds p w 1) (hψ : ∀ a, PatchBounds (ψ a) B (P a))
    (hψc : ∀ a, Continuous (ψ a)) (hwc : Continuous w) (hh : h ≠ 0) :
    ‖∑ a, patchMeanNormal p B (ψ a) w h
      (fun c z ↦ refinedKernelPrefix (D a) J (c, z))‖ ≤
      ‖∑ a, ∑ c, ∫ z : Point,
        ψ a z • atomNormal (refinedKernelPrefix (D a) J (c, z))‖ :=
  norm_sum_patchMeanNormal_le_unmasked hw hψ hψc hwc hh _
    (fun a _ ↦ (continuous_refinedKernelPrefix (D a) J).comp
      (continuous_const.prodMk continuous_id))

end JanetCartan.Sampling.MeanNormalBound
