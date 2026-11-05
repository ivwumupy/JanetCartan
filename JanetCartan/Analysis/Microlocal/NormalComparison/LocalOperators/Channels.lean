module

public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.MatrixKernel

/-!
# Realization of the exact transport channels

Actual bounded operators with the literal `fullNormalAmplitudeKernel` and the
original `pairedTransportCoefficient` of `app:ch_osc:prop:osc-normal`, Step 2.
The fixed L∞ symbols use only the mask value and first derivative bounds.
This module constructs the channels; `LocalOperators.Derivative` identifies
the exact channels with the derivative within the parameter interval.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Frobenius
namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}
local notation "E" => Euclidean n

/-- Construct the exact full normal channels at one admissible parameter,
using fixed mask representatives. This is the operator realization of the
coefficients in Step 2 of `app:ch_osc:prop:osc-normal`; no derivative identity
or frequency-uniform bound is asserted by this construction. -/
theorem UniformNormalData.exists_uniformTransportChannels_at
    (F : UniformNormalData G C) (K : ℝ) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {m : E → ℝ} (hm : ContDiffOn ℝ ∞ m G.D)
    (g : Option (Fin n) → Lp ℂ ∞ (volume.restrict G.D))
    (hg : ∀ k, g k =ᵐ[volume.restrict G.D] compactTransportMask m k)
    (χ : E → E → ℂ) (hχ : ContDiff ℝ ∞ (Function.uncurry χ))
    (hsχ : tsupport (Function.uncurry χ) ⊆ G.X ×ˢ G.D) :
    ∃ N : Option (Fin n) → NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r,
      ∀ k f i, (N k f) i =ᵐ[volume] fun x ↦ ∑ j,
        fullNormalAmplitudeKernel (μ := volume.restrict G.D)
          (normalizedOscillatoryKernel (normalOperatorScale n K) K (F.phase ε) χ)
          (fun u z ↦ F.pairedTransportCoefficient ε k u z i j) (g k) (f j) x := by
  let t := normalizedOscillatoryKernel (normalOperatorScale n K) K (F.phase ε) χ
  have ht : ContDiff ℝ ∞ (Function.uncurry t) :=
    F.cutoffKernel_contDiff hε _ K hχ hsχ
  let c := fun k i j (p : (E × E) × E) ↦
    F.extendedTransportCoefficient ε k (p.1.1, (p.1.2, p.2)) i j
  have hc k i j : ContDiff ℝ ∞ (c k i j) :=
    (matrixEntryEvaluation i j).contDiff.comp
      ((F.extendedTransportCoefficient_contDiff hε k).comp
        (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)))
  let H := fun k i j (p : (E × E) × E) ↦
    t p.1.1 p.2 * c k i j p * star (t p.1.2 p.2) * compactTransportMask m k p.2
  have hH k i j : ContDiffOn ℝ ∞ (H k i j) (univ ×ˢ G.D) :=
    (((ht.comp (contDiff_fst.fst.prodMk contDiff_snd)).mul (hc k i j)).mul
      (Complex.conjCLE.contDiff.comp
        (ht.comp (contDiff_fst.snd.prodMk contDiff_snd)))).contDiffOn.mul
          ((contDiffOn_compactTransportMask G.isOpen_D hm k).comp contDiffOn_snd
            (fun _ hp ↦ hp.2))
  have hs k i j p (hp : p ∉ (G.X₀ ×ˢ G.X₀) ×ˢ G.D₀) : H k i j p = 0 := by
    have hz : F.extendedTransportCoefficient ε k (p.1.1, (p.1.2, p.2)) = 0 := by
      by_contra hn
      have h := F.extendedTransportCoefficient_support hε k hn
      exact hp ⟨⟨h.1, h.2.1⟩, h.2.2⟩
    simp [H, c, hz]
  obtain ⟨N, hN, _, _⟩ := exists_compactIntegratedChannels G.isOpen_D
    G.compact_X₀ G.compact_D₀ G.D₀_subset H hH hs
  refine ⟨N, ?_⟩
  intro k f i
  refine (hN k f i).trans (Eventually.of_forall fun x ↦ ?_)
  apply Finset.sum_congr rfl
  intro j _
  unfold fullNormalAmplitudeKernel
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  congr 1
  apply integral_congr_ae
  filter_upwards [hg k] with u hu
  simp only [H, c, t, hu, pairedTransportCoefficient, pairedNormalAmplitude_pairedPosition]

/-- One set of L∞ representatives works for every parameter in the closed
interval, and realizes every exact transport channel. Only the displayed
first mask derivative bound from `app:ch_osc:prop:osc-normal` is used. -/
theorem UniformNormalData.exists_uniformTransportChannels
    (F : UniformNormalData G C) (K : ℝ)
    {m : E → ℝ} (hm : ContDiffOn ℝ ∞ m G.D)
    {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L)
    (hmask : ∀ u ∈ G.D, 0 ≤ m u ∧ m u ≤ 1)
    (hderiv : ∀ u ∈ G.D, ‖fderiv ℝ m u‖ ≤ L / h)
    (χ : E → E → ℂ) (hχ : ContDiff ℝ ∞ (Function.uncurry χ))
    (hsχ : tsupport (Function.uncurry χ) ⊆ G.X ×ˢ G.D) :
    ∃ g : Option (Fin n) → Lp ℂ ∞ (volume.restrict G.D),
      (∀ k, g k =ᵐ[volume.restrict G.D] compactTransportMask m k) ∧
      ‖g none‖ ≤ 1 ∧ (∀ j, ‖g (some j)‖ ≤ L / h) ∧
      ∀ ε ∈ Icc 0 G.ε₀,
        ∃ N : Option (Fin n) → NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r,
          ∀ k f i, (N k f) i =ᵐ[volume] fun x ↦ ∑ j,
            fullNormalAmplitudeKernel (μ := volume.restrict G.D)
              (normalizedOscillatoryKernel (normalOperatorScale n K) K (F.phase ε) χ)
              (fun u z ↦ F.pairedTransportCoefficient ε k u z i j) (g k) (f j) x := by
  obtain ⟨g₀, g₁, hg₀, hb₀, hg₁, hb₁⟩ := exists_mask_derivative_symbols G.isOpen_D m
    (hm.of_le (by simp)) hh hL hmask hderiv
  let g : Option (Fin n) → Lp ℂ ∞ (volume.restrict G.D) := fun k ↦
    match k with
    | none => g₀
    | some j => g₁ j
  have hg (k) : g k =ᵐ[volume.restrict G.D] compactTransportMask m k := by
    cases k with
    | none => exact hg₀
    | some j => exact hg₁ j
  exact ⟨g, hg, hb₀, hb₁, fun ε hε ↦
    F.exists_uniformTransportChannels_at K hε hm g hg χ hχ hsχ⟩

end JanetCartan.NormalComparison
