module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundQuadrature
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.BoundedSymbols

/-!
# Literal colored carrier masks

Range, smoothness, and the exact partition on the original patch support for
`app:ch_waves:eq:colored-normal-comparison`. These are the existing finite
`BackgroundQuadrature.coloredBlockMask`, with the actual convolved-box window.
No new mask interface or truncation is introduced.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace JanetCartan.Sampling.ColoredNormalComparison
open SeparatedSampling LatticeQuadrature BackgroundQuadrature

/-- Regrouping the literal finite block partition by its original colors
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem sum_coloredBlockMask (p : ℕ) (s : Finset Lattice) (w : ℝ → ℝ)
    (h : ℝ) (z : Point) :
    ∑ c, coloredBlockMask p s w h c z = ∑ q ∈ s, blockWeight w h q z := by
  simpa using (sum_blockWeight_eq_colored_masks p s w h
    (fun _ _ ↦ (1 : ℝ)) z).symm

/-- Nonnegativity of each actual colored mask
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem coloredBlockMask_nonneg {p : ℕ} (s : Finset Lattice) {w : ℝ → ℝ}
    (hw : ∀ t, 0 ≤ w t) (h : ℝ) (c : Fin 3 → Fin (p + 1)) (z : Point) :
    0 ≤ coloredBlockMask p s w h c z := by
  exact Finset.sum_nonneg fun _ _ ↦ Finset.prod_nonneg fun _ _ ↦ hw _

/-- The convolved-box partition bounds every finite colored submask by one,
independently of the number of blocks and the mesh
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem coloredBlockMask_le_one {κ : ℝ → ℝ} (hi : Integrable κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t) {p : ℕ} (hp : 0 < p)
    (s : Finset Lattice) (h : ℝ) (c : Fin 3 → Fin (p + 1)) (z : Point) :
    coloredBlockMask p s (convolvedBoxWindow κ p) h c z ≤ 1 := by
  exact sum_le_hasSum (s.filter fun q ↦ color p q = c)
    (fun q _ ↦ Finset.prod_nonneg fun i _ ↦ convolvedBoxWindow_nonneg hn p _)
    (hasSum_productWindow_sub hi hm hp (fun i ↦ z i / h))

/-- All colors sum to one on the support of the unchanged patch weight.
The finite block ceiling loses no term of the full translated partition
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem sum_coloredBlockMask_eq_one {κ : ℝ → ℝ} (hi : Integrable κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Set.Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {ψ : Point → ℝ} {B P : ℝ}
    (hψ : PatchBounds ψ B P) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    {z : Point} (hz : z ∈ Function.support ψ) :
    ∑ c, coloredBlockMask p (integerCube (blockCutoff p B h))
      (convolvedBoxWindow κ p) h c z = 1 := by
  rw [sum_coloredBlockMask]
  apply (hasSum_sum_of_ne_finset_zero ?_).unique
    (hasSum_productWindow_sub hi hm hp (fun i ↦ z i / h))
  intro q hq
  exact (mul_eq_zero.mp (patch_mul_blockWeight_eq_zero_outside
    (convolvedBoxWindow_bounds hi hm hn hk hp) hψ hh hh₁ hq z)).resolve_left hz

/-- Smoothness of each actual translated block, without bounds on any higher
derivatives (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem contDiff_blockWeight {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (h : ℝ) (q : Lattice) : ContDiff ℝ ∞ (blockWeight w h q) := by
  apply contDiff_prod
  intro i _
  exact hw.comp (((contDiff_apply ℝ (fun _ : Fin 3 ↦ ℝ) i).div_const h).sub
    contDiff_const)

/-- Each finite colored mask of the fixed convolved-box window is smooth.
The derivative budget needed by the normal estimate is only first order
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem contDiff_coloredBlockMask {κ : ℝ → ℝ} (hc : HasCompactSupport κ)
    (hs : ContDiff ℝ ∞ κ) (p : ℕ) (s : Finset Lattice) (h : ℝ)
    (c : Fin 3 → Fin (p + 1)) :
    ContDiff ℝ ∞ (coloredBlockMask p s (convolvedBoxWindow κ p) h c) := by
  apply ContDiff.sum
  intro q _
  exact contDiff_blockWeight (contDiff_convolvedBoxWindow hc hs p) h q

/-- The literal masks, pulled back to the full normal input coordinates, have
exact L∞ representatives of norm at most one. The map `z` retains the three
carrier coordinates (including any fixed spectators). No derivative estimate
or normal estimate is assumed here
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_coloredBlockMask_symbols {κ : ℝ → ℝ} (hc : HasCompactSupport κ)
    (hs : ContDiff ℝ ∞ κ) (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    {p : ℕ} (hp : 0 < p) {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (s : Finset Lattice) (h : ℝ) (z : EuclideanSpace ℝ (Fin n) → Point)
    (hz : Continuous z) :
    ∃ g : (Fin 3 → Fin (p + 1)) → Lp ℂ ∞ (volume.restrict D),
      (∀ c, g c =ᵐ[volume.restrict D] fun u ↦
        (coloredBlockMask p s (convolvedBoxWindow κ p) h c (z u) : ℂ)) ∧
      ∀ c, ‖g c‖ ≤ 1 := by
  have hi : Integrable κ := hs.continuous.integrable_of_hasCompactSupport hc
  have hc' (c : Fin 3 → Fin (p + 1)) :
      AEStronglyMeasurable (fun u ↦
        (coloredBlockMask p s (convolvedBoxWindow κ p) h c (z u) : ℂ))
        (volume.restrict D) :=
    (Complex.continuous_ofReal.comp
      ((contDiff_coloredBlockMask hc hs p s h c).continuous.comp hz)).aestronglyMeasurable
  have hb (c : Fin 3 → Fin (p + 1)) :
      ∀ᵐ u ∂volume.restrict D,
        ‖(coloredBlockMask p s (convolvedBoxWindow κ p) h c (z u) : ℂ)‖ ≤ 1 := by
    filter_upwards [] with u
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (coloredBlockMask_nonneg s (convolvedBoxWindow_nonneg hn p) h c (z u))]
    exact coloredBlockMask_le_one hi hm hn hp s h c (z u)
  exact ⟨fun c ↦ AmplitudeBound.boundedSymbol _ (hc' c) 1 (hb c),
    fun c ↦ AmplitudeBound.boundedSymbol_coeFn _ (hc' c) 1 (hb c),
    fun c ↦ AmplitudeBound.norm_boundedSymbol_le _ (hc' c) 1 (hb c) zero_le_one⟩

end JanetCartan.Sampling.ColoredNormalComparison
