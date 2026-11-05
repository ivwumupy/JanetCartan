module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.MaskDerivative
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.TransportEndpoint
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.OutputTransfer

/-!
# Colored-to-transport comparison from primitive homotopy data

The finite-prefix deduction of `app:ch_waves:eq:colored-normal-comparison`.
The translated masks, their first derivative bounds and their partition are
proved for the literal convolved-box window. The endpoint is deduced from
phase and amplitude equalities, never from an assumed normal equality.

`jc-simultaneous-sampling` must instantiate the same `UniformNormalData` with
the actual quotient phase and measured WKB amplitudes. In particular its
common-history bounds, first parameter jets and inverse Jacobian derivative
remain obligations of `jc-full-phase-charts`, `jc-leading-wave`,
`jc-raw-primary-fields` and `jc-current-coefficient-scale`. The constant below
precedes the family, radial labels, spectator offset, mesh and fixed ceiling.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace JanetCartan.Sampling.ColoredNormalComparison
open NormalComparison RawInputPartition SeparatedSampling LatticeQuadrature BackgroundQuadrature

variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- The complete colored prefix, using the original half-scale dyadic labels
and the quotient parameter `(R c * lam)⁻¹ * dyadicScale j`
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def coloredPrefixNormal {Color : Type*} [Fintype Color]
    (F : Color → ℕ → UniformNormalData G C) (R : Color → ℝ)
    (g : Color → Lp ℂ ∞ (volume.restrict G.D)) (lam : ℝ) (J : ℕ) :
    NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r :=
  ∑ c, ∑ j ∈ Finset.range J,
    (F c j).uniformOscillatoryNormalOperator (dyadicScale j) (g c)
      ((R c * lam)⁻¹ * dyadicScale j)

/-- The uncolored transport normal on exactly the same bands and cutoffs
(`app:ch_waves:eq:colored-normal-comparison`). -/
def transportPrefixNormal (F₀ : ℕ → UniformNormalData G C) (J : ℕ) :
    NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r :=
  ∑ j ∈ Finset.range J, ((F₀ j).uniformOscillatoryOperator (dyadicScale j) 0).comp
    ((F₀ j).uniformOscillatoryOperator (dyadicScale j) 0).adjoint

/-- The colored-to-transport estimate with the literal masks and no mask
regularity or operator-comparison premise. The same exact L∞ symbols serve
every prefix under the fixed sample ceiling. Only primitive endpoint phase,
amplitude and patch-support equalities remain for the actual wave producer.
No high-pass transition, physical position, radial label, or cutoff is changed
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_colored_prefix_transport_bound (G : UniformNormalGeometry n r)
    (C : ℕ → ℝ) {κ : ℝ → ℝ} (hc : HasCompactSupport κ)
    (hs : ContDiff ℝ ∞ κ) (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) (Z : Euclidean n →L[ℝ] Point)
    {Rmin : ℝ} (hRmin : 0 < Rmin) :
    ∃ A > 0, ∀ (F : (Fin 3 → Fin (p + 1)) → ℕ → UniformNormalData G C)
      (F₀ : ℕ → UniformNormalData G C) (R : (Fin 3 → Fin (p + 1)) → ℝ)
      (Rmax : ℝ), (∀ c, R c ∈ Icc Rmin Rmax) →
      ∀ (ψ : Point → ℝ) (B P : ℝ), PatchBounds ψ B P →
      ∀ (z₀ : Point) (h : ℝ), 0 < h → h ≤ 1 →
      ∀ g : (Fin 3 → Fin (p + 1)) → Lp ℂ ∞ (volume.restrict G.D),
      (∀ c, g c =ᵐ[volume.restrict G.D] fun u ↦
        (coloredBlockMask p (integerCube (blockCutoff p B h))
          (convolvedBoxWindow κ p) h c (z₀ + Z u) : ℂ)) →
      ∀ lam Λ : ℝ, 0 < lam → 1 ≤ Λ → Λ / (Rmin * lam) ≤ G.ε₀ →
      ∀ J ≤ cutoffCount Λ,
      (∀ c j, j ∈ Finset.range J → ∀ x ∈ G.X, ∀ u ∈ G.D,
        (F c j).phase 0 x u = (F₀ j).phase 0 x u) →
      (∀ c j, j ∈ Finset.range J → ∀ x ∈ G.X, ∀ u ∈ G.D,
        (F c j).amplitude 0 x u = (F₀ j).amplitude 0 x u) →
      (∀ j ∈ Finset.range J, ∀ x u, u ∈ G.D →
        (F₀ j).amplitude 0 x u ≠ 0 → z₀ + Z u ∈ Function.support ψ) →
      ‖coloredPrefixNormal F R g lam J - transportPrefixNormal F₀ J‖ ≤
        A * lam⁻¹ * Λ / h := by
  obtain ⟨L, hL, hderiv⟩ := exists_coloredBlockMask_pullback_fderiv_bound hc hs hm hn hk hp
  obtain ⟨A, hA, hbound⟩ := exists_colored_prefix_homotopy_bound
    (Color := Fin 3 → Fin (p + 1)) G C hRmin (mul_nonneg hL (norm_nonneg Z))
  refine ⟨A, hA, ?_⟩
  intro F F₀ R Rmax hR ψ B P hψ z₀ h hh hh₁ g hg lam Λ hlam hΛ hbuffer
    J hJ hphase hamp hsupport
  let m := fun c u ↦ coloredBlockMask p (integerCube (blockCutoff p B h))
    (convolvedBoxWindow κ p) h c (z₀ + Z u)
  have hi : Integrable κ := hs.continuous.integrable_of_hasCompactSupport hc
  have hm' (c : Fin 3 → Fin (p + 1)) : ContDiffOn ℝ ∞ (m c) G.D :=
    ((contDiff_coloredBlockMask hc hs p _ h c).comp
      (contDiff_const.add Z.contDiff)).contDiffOn
  have hrange (c : Fin 3 → Fin (p + 1)) (u : Euclidean n) (_hu : u ∈ G.D) :
      0 ≤ m c u ∧ m c u ≤ 1 :=
    ⟨coloredBlockMask_nonneg _ (convolvedBoxWindow_nonneg hn p) h c _,
      coloredBlockMask_le_one hi hm hn hp _ h c _⟩
  have hb := hbound F R (fun c ↦ (hR c).1) m hm' h hh hh₁ hrange
    (fun c u _ ↦ hderiv n Z B h hh c z₀ u) g hg lam Λ hlam hΛ hbuffer J hJ
  have he := sum_colored_prefix_normal_zero_eq_transport hi hm hn hk hp hψ hh hh₁
    (fun u ↦ z₀ + Z u) F F₀ J hphase hamp hsupport g hg
  rw [he] at hb
  exact hb

/-- The same deduction on the original vector-valued Lebesgue output and on
both physical real quadratures. The real estimate costs exactly the fixed
factor four; there is no output compression or dimension loss
(`app:ch_waves:eq:colored-normal-comparison`, `app:ch_waves:eq:real-normal`). -/
theorem exists_colored_prefix_sampling_transport_bound (G : UniformNormalGeometry n n)
    (C : ℕ → ℝ) {κ : ℝ → ℝ} (hc : HasCompactSupport κ)
    (hs : ContDiff ℝ ∞ κ) (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) (Z : Euclidean n →L[ℝ] Point)
    {Rmin : ℝ} (hRmin : 0 < Rmin) :
    ∃ A > 0, ∀ (F : (Fin 3 → Fin (p + 1)) → ℕ → UniformNormalData G C)
      (F₀ : ℕ → UniformNormalData G C) (R : (Fin 3 → Fin (p + 1)) → ℝ)
      (Rmax : ℝ), (∀ c, R c ∈ Icc Rmin Rmax) →
      ∀ (ψ : Point → ℝ) (B P : ℝ), PatchBounds ψ B P →
      ∀ (z₀ : Point) (h : ℝ), 0 < h → h ≤ 1 →
      ∀ g : (Fin 3 → Fin (p + 1)) → Lp ℂ ∞ (volume.restrict G.D),
      (∀ c, g c =ᵐ[volume.restrict G.D] fun u ↦
        (coloredBlockMask p (integerCube (blockCutoff p B h))
          (convolvedBoxWindow κ p) h c (z₀ + Z u) : ℂ)) →
      ∀ lam Λ : ℝ, 0 < lam → 1 ≤ Λ → Λ / (Rmin * lam) ≤ G.ε₀ →
      ∀ J ≤ cutoffCount Λ,
      (∀ c j, j ∈ Finset.range J → ∀ x ∈ G.X, ∀ u ∈ G.D,
        (F c j).phase 0 x u = (F₀ j).phase 0 x u) →
      (∀ c j, j ∈ Finset.range J → ∀ x ∈ G.X, ∀ u ∈ G.D,
        (F c j).amplitude 0 x u = (F₀ j).amplitude 0 x u) →
      (∀ j ∈ Finset.range J, ∀ x u, u ∈ G.D →
        (F₀ j).amplitude 0 x u ≠ 0 → z₀ + Z u ∈ Function.support ψ) →
      ‖samplingOutputConjugation n (coloredPrefixNormal F R g lam J) -
        samplingOutputConjugation n (transportPrefixNormal F₀ J)‖ ≤ A * lam⁻¹ * Λ / h ∧
      ‖samplingRealNormal n (coloredPrefixNormal F R g lam J) -
        samplingRealNormal n (transportPrefixNormal F₀ J)‖ ≤ 4 * (A * lam⁻¹ * Λ / h) := by
  obtain ⟨A, hA, hbound⟩ := exists_colored_prefix_transport_bound G C hc hs hm hn hk hp Z hRmin
  refine ⟨A, hA, ?_⟩
  intro F F₀ R Rmax hR ψ B P hψ z₀ h hh hh₁ g hg lam Λ hlam hΛ hbuffer
    J hJ hphase hamp hsupport
  exact sampling_normal_comparison_of_coordinate_bound _ _
    (hbound F F₀ R Rmax hR ψ B P hψ z₀ h hh hh₁ g hg lam Λ hlam hΛ hbuffer
      J hJ hphase hamp hsupport)

end JanetCartan.Sampling.ColoredNormalComparison
