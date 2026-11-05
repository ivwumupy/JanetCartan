module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.FullCoefficientDilation

/-!
# One source scale for local and extended coefficient margins

For `main:prop:seed` and `app:ch_regular:eq:coefficient-extension`, intersect
the proved full-array interval with the finite margins for the fixed affine
extension. The consumer is the common normalized-history seed constructor. It must impose
these margins on the scale selected by the relative normalized mean, and on
every further positive contraction, rather than choose another reference.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ReferenceInitialization.NormalizedHistory
open GeometricProfile ProjectedStressFrame ProtectedFlow FullCoefficientDilation

/-- The actual local and globally extended full arrays meet their prescribed
finite margins at every sufficiently small source scale (`main:prop:seed`,
`app:ch_regular:eq:coefficient-extension`). Both arrays use the literal zero
lower-order background; the extension parameters precede the scale. -/
theorem exists_source_scale_full_and_extended_margin_interval {n : ℕ}
    (G : FlatReference n) {K : Set (Euclidean n)} (hK : IsCompact K)
    (p : BallExtension.Parameters (Euclidean n))
    (orders : Finset ℕ) (margin extendedMargin : ℕ → ℝ)
    (hmargin : ∀ j ∈ orders, 0 < margin j)
    (hextendedMargin : ∀ j ∈ orders, 0 < extendedMargin j)
    {ε₆ cap : ℝ} (hε₆ : 0 < ε₆) (hcap : 0 < cap) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < cap ∧ ρ ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) ρ,
      (∀ j ∈ orders, cNorm K j
        (geometricReducedCoefficients (sourceDilation G.map σ) -
          reducedCoefficientBackground (fun _ _ ↦ 0)) < margin j) ∧
      (∀ i, cNorm K 6 (fun x ↦ projectedStress (sourceDilation G.map σ) x i -
        cubeStress n i) < ε₆) ∧
      ContDiff ℝ ∞ (extendedReducedCoefficients p (fun _ _ ↦ 0)
        (sourceDilation G.map σ)) ∧
      ∀ j ∈ orders, cNorm univ j
        (extendedReducedCoefficients p (fun _ _ ↦ 0) (sourceDilation G.map σ) -
          reducedCoefficientBackground (fun _ _ ↦ 0)) < extendedMargin j := by
  classical
  obtain ⟨Ue, _, _, σe, hσe, _, hgeom, hb⟩ :=
    exists_extendedReducedCoefficients_dilation_bounds G p
  obtain ⟨U, _, _, δ, hδ, hδcap, hδ1, _, hlocal, _⟩ :=
    exists_fullReducedCoefficients_finite_margin_interval G hK orders id margin hmargin
      hε₆ (lt_min hcap hσe)
  choose C hC hbound using hb
  let bounds := insert δ (orders.image (fun j ↦ extendedMargin j / (2 * C j)))
  have hbounds : bounds.Nonempty := Finset.insert_nonempty _ _
  let ρ := bounds.min' hbounds
  have hρ : 0 < ρ := by
    have hp : ∀ t ∈ bounds, 0 < t := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hδ
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
        exact div_pos (hextendedMargin j hj) (mul_pos (by norm_num) (hC j))
    exact hp _ (bounds.min'_mem hbounds)
  have hρδ : ρ ≤ δ := bounds.min'_le _ (Finset.mem_insert_self _ _)
  refine ⟨ρ, hρ, hρδ.trans_lt (hδcap.trans_le (min_le_left _ _)),
    hρδ.trans hδ1, ?_⟩
  intro σ hσ
  have hσδ : σ ≤ δ := hσ.2.trans hρδ
  have hσe : σ ∈ Ioc (0 : ℝ) σe :=
    ⟨hσ.1, hσδ.trans (hδcap.le.trans (min_le_right _ _))⟩
  obtain ⟨_, _, _, _, hraw, hframe⟩ := hlocal σ ⟨hσ.1, hσδ⟩
  refine ⟨hraw, hframe, (hgeom σ hσe).2.2.2, ?_⟩
  intro j hj
  have hh : σ ≤ extendedMargin j / (2 * C j) :=
    hσ.2.trans (bounds.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩)))
  have hmul := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (hC j))).mp hh
  have hm := hextendedMargin j hj
  exact ((hbound j σ hσe).1).trans_lt (by nlinarith)

end JanetCartan.ReferenceInitialization.NormalizedHistory
