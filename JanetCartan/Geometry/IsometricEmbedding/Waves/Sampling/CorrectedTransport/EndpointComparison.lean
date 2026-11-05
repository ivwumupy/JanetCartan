module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.CrossAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColoredApplication.WeightedEndpoint

/-!
# Original patch comparison for fixed-rate corrected homotopies

Each color may have its own fixed-response path. Their common zero amplitude
and phase identify the uncolored normal exactly. The existing derivative
comparison then gives every prefix bound on the unchanged patch-weighted
symbols and full output, including both physical real quadratures.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped ContDiff ENNReal
namespace JanetCartan.Sampling.CorrectedTransport
open NormalComparison AmplitudeBound RawInputPartition ColoredNormalComparison
open SeparatedSampling LatticeQuadrature BackgroundQuadrature
open MeasuredAmplitude.ColoredApplication

/-- Equality of the literal zero phase and amplitude identifies the weighted
normal, independently of the remaining homotopy
(`app:ch_waves:eq:colored-normal-comparison`). -/
private theorem uniformNormal_zero_eq_of_fields {n : ℕ}
    {G : UniformNormalGeometry n n} {C : ℕ → ℝ}
    (F F₀ : UniformNormalData G C) (K : ℝ)
    (g : Lp ℂ ∞ (volume.restrict G.D))
    (hp : F.phase 0 = F₀.phase 0) (ha : F.amplitude 0 = F₀.amplitude 0) :
    F.uniformOscillatoryNormalOperator K g 0 = F₀.uniformOscillatoryNormalOperator K g 0 := by
  have hz : (0 : ℝ) ∈ Icc 0 G.ε₀ := ⟨le_rfl, G.ε₀_pos.le⟩
  have hT : F.uniformOscillatoryOperator K 0 = F₀.uniformOscillatoryOperator K 0 := by
    ext f i
    filter_upwards [F.uniformOscillatoryOperator_ae_integral K hz f i,
      F₀.uniformOscillatoryOperator_ae_integral K hz f i] with x hx hx₀
    rw [hx, hx₀]
    apply integral_congr_ae
    filter_upwards [] with u
    rw [hp, ha]
  simp only [UniformNormalData.uniformOscillatoryNormalOperator, hT]

/-- Original patch-weighted transport comparison for different fixed-rate
paths with their proved common leading endpoint. The constant precedes every
path, radial rate, frequency and prefix. The equality hypotheses are supplied
by `correctedTransportNormalAmplitude_zero_independent` and the SAME retained
phase constructor (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_fixedRate_colored_prefix_transport_bound {n : ℕ}
    (G : UniformNormalGeometry n n) (C : ℕ → ℝ)
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {φ : Point → ℝ} {B P : ℝ}
    (hφ : PatchBounds φ B P) (hφs : ContDiff ℝ ∞ φ)
    (Z : Euclidean n →L[ℝ] Point) {Rmin : ℝ} (hRmin : 0 < Rmin) :
    ∃ A > 0,
      ∀ (F : (Fin 3 → Fin (p + 1)) → ℕ → UniformNormalData G C)
        (F₀ : ℕ → UniformNormalData G C),
      (∀ c j, (F c j).phase 0 = (F₀ j).phase 0) →
      (∀ c j, (F c j).amplitude 0 = (F₀ j).amplitude 0) →
      ∀ (R : (Fin 3 → Fin (p + 1)) → ℝ), (∀ c, Rmin ≤ R c) →
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
          (F c j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g c)
            ((R c * lam)⁻¹ * (2 : ℝ) ^ j)
        let E₀ := ∑ j ∈ Finset.range J,
          (F₀ j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) g₀ 0
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
  intro F F₀ hphase hamp R hR z₀ h hh hh₁ g g₀ hg hg₀ lam Λ hlam hΛ hbuffer J hJ
  let m := fun c u ↦ φ (z₀ + Z u) *
    coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p) h c (z₀ + Z u)
  have hg' : ∀ c, g c =ᵐ[volume.restrict G.D] fun u ↦ (m c u : ℂ) := by
    intro c
    simpa only [m, Complex.ofReal_mul] using hg c
  have hbound := hb F R hR m
    (fun c ↦ (hmult z₀ h hh hh₁ c).1.contDiffOn) h hh hh₁
    (fun c u _ ↦ (hmult z₀ h hh hh₁ c).2.1 u)
    (fun c u _ ↦ (hmult z₀ h hh hh₁ c).2.2 u) g hg'
    lam Λ hlam hΛ hbuffer J hJ
  have heq (c j) : (F c j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g c) 0 =
      (F₀ j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g c) 0 :=
    uniformNormal_zero_eq_of_fields (F c j) (F₀ j) _ _ (hphase c j) (hamp c j)
  simp_rw [heq] at hbound
  rw [sum_patch_colored_zero_eq_uncolored
    (hs.continuous.integrable_of_hasCompactSupport hc) hm hn hk hp hφ hh hh₁
    (fun u ↦ z₀ + Z u) F₀ J g g₀ hg hg₀] at hbound
  exact ⟨hbound, sampling_normal_comparison_of_coordinate_bound _ _ hbound⟩

end JanetCartan.Sampling.CorrectedTransport
