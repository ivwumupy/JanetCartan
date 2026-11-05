module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.FullCoefficientDilation

/-!
# One source scale for local and extended coefficient margins

For `main:prop:seed` and `app:ch_regular:eq:coefficient-extension`, intersect
the proved full-array interval with the finite margins for the fixed affine
extension. The consumer is `exists_scaled_reference_geometric_neighborhood_with_full_margins`;
carrier geometry fixes the cutoff parameters before this scale is chosen.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ReferenceInitialization.CommonMargins
open GeometricProfile ProjectedStressFrame ProtectedFlow FullCoefficientDilation

/-- The actual local and globally extended full arrays meet their prescribed
finite margins at the same source scale (`main:prop:seed`,
`app:ch_regular:eq:coefficient-extension`). Both arrays use the literal zero
lower-order background; the extension parameters precede the scale. -/
theorem exists_source_scale_full_and_extended_margins {n : ℕ}
    (G : FlatReference n) {K : Set (Euclidean n)} (hK : IsCompact K)
    (p : BallExtension.Parameters (Euclidean n))
    (orders : Finset ℕ) (margin extendedMargin : ℕ → ℝ)
    (hmargin : ∀ j ∈ orders, 0 < margin j)
    (hextendedMargin : ∀ j ∈ orders, 0 < extendedMargin j)
    {ε₆ cap : ℝ} (hε₆ : 0 < ε₆) (hcap : 0 < cap) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < cap ∧ ρ ≤ 1 ∧
      (∀ j ∈ orders, cNorm K j
        (geometricReducedCoefficients (sourceDilation G.map ρ) -
          reducedCoefficientBackground (fun _ _ ↦ 0)) < margin j) ∧
      (∀ i, cNorm K 6 (fun x ↦ projectedStress (sourceDilation G.map ρ) x i -
        cubeStress n i) < ε₆) ∧
      ContDiff ℝ ∞ (extendedReducedCoefficients p (fun _ _ ↦ 0)
        (sourceDilation G.map ρ)) ∧
      ∀ j ∈ orders, cNorm univ j
        (extendedReducedCoefficients p (fun _ _ ↦ 0) (sourceDilation G.map ρ) -
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
  have hρe : ρ ∈ Ioc (0 : ℝ) σe :=
    ⟨hρ, hρδ.trans (hδcap.le.trans (min_le_right _ _))⟩
  obtain ⟨_, _, _, _, hraw, hframe⟩ := hlocal ρ ⟨hρ, hρδ⟩
  refine ⟨ρ, hρ, hρδ.trans_lt (hδcap.trans_le (min_le_left _ _)),
    hρδ.trans hδ1, hraw, hframe, (hgeom ρ hρe).2.2.2, ?_⟩
  intro j hj
  have hh : ρ ≤ extendedMargin j / (2 * C j) :=
    bounds.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
  have hmul := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (hC j))).mp hh
  have hm := hextendedMargin j hj
  exact ((hbound j ρ hρe).1).trans_lt (by nlinarith)

end JanetCartan.ReferenceInitialization.CommonMargins
