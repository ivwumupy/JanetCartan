module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.FinalMask

/-!
# A fixed neighborhood of the buffered source product

The source product in `app:ch_regular:thm:no-return` has a physical and an
angular buffer. Compactness of this fixed product, rather than of coefficient
fields, gives the neighborhood needed at the first non-diagonal step of
`app:ch_regular:lem:finite-chain`. Positive homogeneity applies the SAME retained
source cover to every radial scale in that neighborhood.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open ProtectedFlow ActualCarriers HamiltonPhase PhaseCover

variable {d : ℕ}

/-- A source with fixed physical and angular buffers has a common closed
neighborhood, still in the prescribed source buffer and protected cone, with
positive annular bounds. The inputs are satisfied by the paper's compact
product over `tsupport χ₂`, with its fixed angular support inside `Ω₁`
(`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`). -/
theorem exists_buffered_source_neighborhood
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hS : IsCompact S)
    {r : ℝ} {Ω Γ : Set (Euclidean (d + 1))}
    (hsource : ∀ p ∈ S, p.1 ∈ ball 0 r ∧ p.2 ≠ 0 ∧
      normalizedCovector p.2 ∈ interior Ω)
    (hΩΓ : Ω ⊆ interior Γ)
    {V : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hV : IsOpen V) (hSV : S ⊆ V) :
    ∃ σ > (0 : ℝ), ∃ a > (0 : ℝ), ∃ b > a,
      ∀ p ∈ cthickening σ S,
        p ∈ V ∧ p.1 ∈ ball 0 r ∧ p.2 ≠ 0 ∧
        normalizedCovector p.2 ∈ Ω ∧
        p ∈ physicalProtectedRegion Γ ∧ a ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ b := by
  let O := V ∩ (Prod.fst ⁻¹' ball (0 : Euclidean (d + 1)) r) ∩
    physicalProtectedRegion Ω
  have hO : IsOpen O := (hV.inter (isOpen_ball.preimage continuous_fst)).inter
    (isOpen_physicalProtectedRegion Ω)
  have hSO : S ⊆ O := by
    intro p hp
    obtain ⟨hx, hn, hΩ⟩ := hsource p hp
    exact ⟨⟨hSV hp, hx⟩, hn, hΩ⟩
  obtain ⟨σ, hσ, hσO⟩ := hS.exists_cthickening_subset_open hO hSO
  obtain ⟨a, ha, hlow⟩ := CompatibleResponse.exists_uniform_positive_bound hS.cthickening
    continuous_snd.norm.continuousOn
    (fun p hp ↦ norm_pos_iff.mpr (hσO hp).2.1)
  obtain ⟨b, hhigh⟩ := hS.cthickening.exists_bound_of_continuousOn
    (continuous_snd.continuousOn : ContinuousOn
      (Prod.snd : Euclidean (d + 1) × Euclidean (d + 1) → Euclidean (d + 1))
        (cthickening σ S))
  refine ⟨σ, hσ, a, ha, max a b + 1, by linarith [le_max_left a b], ?_⟩
  intro p hp
  obtain ⟨⟨hpV, hpx⟩, hpn, hpΩ⟩ := hσO hp
  exact ⟨hpV, hpx, hpn, interior_subset hpΩ, ⟨hpn, hΩΓ (interior_subset hpΩ)⟩,
    hlow p hp, (hhigh p hp).trans ((le_max_right a b).trans (by linarith))⟩

/-- The exact retained source cover covers every nonzero radial rescaling
of the buffered angular product. The scale interval is derived from the
source annulus and the retained comparison-gradient bounds; it is not an
extra graph-cover hypothesis (`app:ch_regular:thm:no-return`). -/
theorem comparison_source_scaled_cover {I : Type*}
    {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1)}
    (hQ : ContDiff ℝ ∞ Q) {g : I → ComparisonGeometry (Euclidean (d + 1))}
    (C : (i : I) → ComparisonChart
      (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g i))
    {r a b c G : ℝ} (hc : 0 < c) (hG : 0 < G)
    {Ω : Set (Euclidean (d + 1))}
    (hcover : ∀ z ∈ closedBall 0 r ×ˢ Ω, normalizedSymbol Q z = 0 →
      z ∈ positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ)
    (hgraph : ∀ η x, x ∈ ball 0 r →
      c ≤ ‖ComparisonChart.familyGradient C η x‖ ∧
        ‖ComparisonChart.familyGradient C η x‖ ≤ G)
    {p : Euclidean (d + 1) × Euclidean (d + 1)}
    (hx : p.1 ∈ ball 0 r) (hne : p.2 ≠ 0)
    (hΩ : normalizedCovector p.2 ∈ Ω) (ha : a ≤ ‖p.2‖) (hb : ‖p.2‖ ≤ b)
    (hp : normalizedSymbol Q p = 0) :
    ∃ η : ComparisonGeometry.ParameterFamily g, ∃ scale ∈ Icc (a / G) (b / c),
      p.2 = scale • ComparisonChart.familyGradient C η p.1 := by
  have hnorm : 0 < ‖p.2‖ := norm_pos_iff.mpr hne
  have hnormalized : normalizedSymbol Q (p.1, normalizedCovector p.2) = 0 := by
    rw [normalizedCovector, normalizedSymbol_pos_homogeneous Q p (inv_pos.mpr hnorm),
      hp, mul_zero]
  obtain ⟨_, η, _, t, ht, he⟩ := hcover (p.1, normalizedCovector p.2)
    ⟨ball_subset_closedBall hx, hΩ⟩ hnormalized
  dsimp only at he
  let scale := ‖p.2‖ * t
  have hs : 0 < scale := mul_pos hnorm ht
  have heq : p.2 = scale • ComparisonChart.familyGradient C η p.1 := by
    calc
      p.2 = ‖p.2‖ • normalizedCovector p.2 := by
        simp [normalizedCovector, smul_smul, ne_of_gt hnorm]
      _ = scale • ComparisonChart.familyGradient C η p.1 := by rw [he, smul_smul]
  have hnormeq : ‖p.2‖ = scale * ‖ComparisonChart.familyGradient C η p.1‖ := by
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  obtain ⟨hl, hu⟩ := hgraph η p.1 hx
  refine ⟨η, scale, ⟨(div_le_iff₀ hG).mpr ?_, (le_div_iff₀ hc).mpr ?_⟩, heq⟩
  · nlinarith
  · nlinarith

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
