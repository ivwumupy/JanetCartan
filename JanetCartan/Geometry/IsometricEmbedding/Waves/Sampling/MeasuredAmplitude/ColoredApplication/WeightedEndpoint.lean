module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColoredApplication.PowTwoComparison
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.OutputTransfer

/-!
# The uncolored patch multiplier at the retained zero endpoint

Apply the proved patch-weighted multiplier bounds and the actual `2^j`
homotopy estimate to one common normal family, as supplied by
`exists_full_retained_measuredKernel_mean`. The color sum at zero is proved
by linearity in the multiplier and the literal finite partition. This step
does not assume a normal identity or comparison estimate. Its consumer is
the full retained application of `app:ch_waves:eq:colored-normal-comparison`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff ENNReal

namespace JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
open NormalComparison AmplitudeBound RawInputPartition ColoredNormalComparison
open SeparatedSampling LatticeQuadrature BackgroundQuadrature

private theorem sum_normal_symbol {n r : ℕ} {G : UniformNormalGeometry n r}
    {C : ℕ → ℝ} (N : UniformNormalData G C) (K ε : ℝ)
    {Color : Type*} [Fintype Color] (g : Color → Lp ℂ ∞ (volume.restrict G.D)) :
    ∑ c, N.uniformOscillatoryNormalOperator K (g c) ε =
      N.uniformOscillatoryNormalOperator K (∑ c, g c) ε := by
  simp only [UniformNormalData.uniformOscillatoryNormalOperator, multiplicationOperator,
    map_sum, ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.finsetSum_comp]

/-- The colored zero endpoint equals the uncolored patch-weighted normal on
the same family and the same bands. The auxiliary carrier cutoff stays in
the amplitude; the original patch weight stays in the multiplier
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem sum_patch_colored_zero_eq_uncolored {n r : ℕ}
    {G : UniformNormalGeometry n r} {C : ℕ → ℝ}
    {κ : ℝ → ℝ} (hi : Integrable κ) (hm : ∫ t, κ t = 1)
    (hn : ∀ t, 0 ≤ κ t) (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {φ : Point → ℝ} {B P : ℝ}
    (hφ : PatchBounds φ B P) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (z : Euclidean n → Point) (Ns : ℕ → UniformNormalData G C) (J : ℕ)
    (g : (Fin 3 → Fin (p + 1)) → Lp ℂ ∞ (volume.restrict G.D))
    (g₀ : Lp ℂ ∞ (volume.restrict G.D))
    (hg : ∀ c, g c =ᵐ[volume.restrict G.D] fun u ↦
      (φ (z u) * coloredBlockMask p (integerCube (blockCutoff p B h))
        (convolvedBoxWindow κ p) h c (z u) : ℂ))
    (hg₀ : g₀ =ᵐ[volume.restrict G.D] fun u ↦ (φ (z u) : ℂ)) :
    ∑ c, ∑ j ∈ Finset.range J,
      (Ns j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g c) 0 =
    ∑ j ∈ Finset.range J,
      (Ns j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) g₀ 0 := by
  have hsum : ∑ c, g c = g₀ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_finsetSum Finset.univ g, eventually_all.mpr hg, hg₀]
      with u hsum hu hu₀
    rw [hsum, Finset.sum_apply, hu₀]
    simp_rw [hu, ← Complex.ofReal_mul]
    rw [← Complex.ofReal_sum, sum_patch_mul_coloredBlockMask hi hm hn hk hp hφ hh hh₁]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [sum_normal_symbol, hsum]

/-- Comparison to the uncolored patch-weighted zero endpoint for the SAME
normal family, using the literal original masks. The constant is chosen
before the family, radial labels, spectator offset, frequency and ceiling.
The masks' first derivative bound and their zero-endpoint partition are
conclusions of the patch and convolved-window producers, not assumptions.
The estimate is on full output, with both real quadratures and factor four
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_patch_powTwo_prefix_transport_bound {n : ℕ}
    (G : UniformNormalGeometry n n) (C : ℕ → ℝ)
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {φ : Point → ℝ} {B P : ℝ}
    (hφ : PatchBounds φ B P) (hφs : ContDiff ℝ ∞ φ)
    (Z : Euclidean n →L[ℝ] Point) {Rmin : ℝ} (hRmin : 0 < Rmin) :
    ∃ A > 0, ∀ (Ns : ℕ → UniformNormalData G C)
      (R : (Fin 3 → Fin (p + 1)) → ℝ), (∀ c, Rmin ≤ R c) →
      ∀ z₀ : Point, ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ (g : (Fin 3 → Fin (p + 1)) → Lp ℂ ∞ (volume.restrict G.D))
        (g₀ : Lp ℂ ∞ (volume.restrict G.D)),
      (∀ c, g c =ᵐ[volume.restrict G.D] fun u ↦
        (φ (z₀ + Z u) * coloredBlockMask p (integerCube (blockCutoff p B h))
          (convolvedBoxWindow κ p) h c (z₀ + Z u) : ℂ)) →
      (g₀ =ᵐ[volume.restrict G.D] fun u ↦ (φ (z₀ + Z u) : ℂ)) →
      ∀ lam Λ : ℝ, 0 < lam → 1 ≤ Λ → 2 * Λ / (Rmin * lam) ≤ G.ε₀ →
      ∀ J ≤ cutoffCount Λ,
        let E := ∑ c, ∑ j ∈ Finset.range J,
          (Ns j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g c)
            ((R c * lam)⁻¹ * (2 : ℝ) ^ j)
        let E₀ := ∑ j ∈ Finset.range J,
          (Ns j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) g₀ 0
        ‖E - E₀‖ ≤ A * lam⁻¹ * Λ / h ∧
        ‖samplingOutputConjugation n E - samplingOutputConjugation n E₀‖ ≤
          A * lam⁻¹ * Λ / h ∧
        ‖samplingRealNormal n E - samplingRealNormal n E₀‖ ≤
          4 * (A * lam⁻¹ * Λ / h) := by
  obtain ⟨L, hL, hmult⟩ :=
    exists_patch_coloredBlockMask_pullback_bounds hc hs hm hn hk hp hφ hφs Z
  obtain ⟨A, hA, hb⟩ := exists_bounded_powTwo_prefix_homotopy_bound
    (Color := Fin 3 → Fin (p + 1)) G C hRmin
    ((hφ.nonneg 0).trans (hφ.le_bound 0)) hL
  refine ⟨A, hA, ?_⟩
  intro Ns R hR z₀ h hh hh₁ g g₀ hg hg₀ lam Λ hlam hΛ hbuffer J hJ
  let m := fun c u ↦ φ (z₀ + Z u) *
    coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p) h c (z₀ + Z u)
  have hg' : ∀ c, g c =ᵐ[volume.restrict G.D] fun u ↦ (m c u : ℂ) := by
    intro c
    simpa only [m, Complex.ofReal_mul] using hg c
  have hbound := hb (fun _ ↦ Ns) R hR m
    (fun c ↦ (hmult z₀ h hh hh₁ c).1.contDiffOn) h hh hh₁
    (fun c u _ ↦ (hmult z₀ h hh hh₁ c).2.1 u)
    (fun c u _ ↦ (hmult z₀ h hh hh₁ c).2.2 u) g hg'
    lam Λ hlam hΛ hbuffer J hJ
  rw [sum_patch_colored_zero_eq_uncolored
    (hs.continuous.integrable_of_hasCompactSupport hc) hm hn hk hp hφ hh hh₁
    (fun u ↦ z₀ + Z u) Ns J g g₀ hg hg₀] at hbound
  exact ⟨hbound, sampling_normal_comparison_of_coordinate_bound _ _ hbound⟩

end JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
