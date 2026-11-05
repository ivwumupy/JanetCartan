module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.FullCoefficientDilation.Extension

/-!
# A common source scale for all fixed reference coefficient margins

The full-array reference margin for `main:prop:seed` and
`app:ch_regular:eq:coefficient-extension`. A finite family of low-order bounds,
a prescribed C6 principal-frame tolerance, and any preassigned positive scale
cap are met by one literal source dilation. Every smaller positive scale works
on the same open neighborhood, so the initialization parent can intersect this
interval with its other geometric thresholds before making its single choice.

This supplies the reference-margin estimate for the regular-sector coefficient
class, `ProtectedFlow.exists_extendedReducedCoefficients_low_neighborhood`, and
`UniformStep`. It does not select carriers or current-map neighborhoods.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ReferenceInitialization.FullCoefficientDilation
open GeometricProfile ProjectedStressFrame ProtectedFlow
variable {n : ℕ}

/-- All sufficiently small positive source scales meet a finite list of
full-array margins and a C6 frame tolerance, strictly below any prescribed cap
(`main:prop:seed`, `app:ch_regular:eq:coefficient-extension`). Indexed orders
allow repeated derivative orders with different margins. The neighborhood is
common to the entire interval; all higher-order estimates remain available. -/
theorem exists_fullReducedCoefficients_finite_margin_interval
    (G : FlatReference n) {K : Set (Euclidean n)} (hK : IsCompact K)
    {ι : Type*} (s : Finset ι) (order : ι → ℕ) (margin : ι → ℝ)
    (hmargin : ∀ j ∈ s, 0 < margin j) {ε₆ cap : ℝ} (hε₆ : 0 < ε₆) (hcap : 0 < cap) :
    ∃ U : Set (Euclidean n), IsOpen U ∧ K ⊆ U ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < cap ∧ δ ≤ 1 ∧
        (∀ σ ∈ Icc (0 : ℝ) δ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ U,
          t • (σ • x) ∈ G.domain.chart n) ∧
        (∀ σ ∈ Ioc (0 : ℝ) δ,
          ContDiff ℝ ∞ (sourceDilation G.map σ) ∧
          IsImmersionOn (sourceDilation G.map σ) U ∧
          HasFullNormalRankOn (sourceDilation G.map σ) U ∧
          ContDiffOn ℝ ∞ (geometricReducedCoefficients (sourceDilation G.map σ)) U ∧
          (∀ j ∈ s, cNorm K (order j)
            (geometricReducedCoefficients (sourceDilation G.map σ) -
              reducedCoefficientBackground (fun _ _ ↦ 0)) < margin j) ∧
          ∀ i, cNorm K 6 (fun x ↦ projectedStress (sourceDilation G.map σ) x i -
            cubeStress n i) < ε₆) ∧
        ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Ioc (0 : ℝ) δ,
          cNorm K m (geometricReducedCoefficients (sourceDilation G.map σ) -
            reducedCoefficientBackground (fun _ _ ↦ 0)) ≤ C * σ ∧
          ∀ i, cNorm K m (fun x ↦ projectedStress (sourceDilation G.map σ) x i -
            cubeStress n i) ≤ C * σ := by
  classical
  obtain ⟨U, hU, hKU, σ₀, hσ₀, hσ₁, hseg, hgeom, hb⟩ :=
    exists_fullReducedCoefficients_dilation_bounds G hK
  choose C hC hbound using hb
  let τ := min σ₀ (min (cap / 2) (ε₆ / (2 * C 6)))
  have hτ : 0 < τ := lt_min hσ₀ (lt_min (by positivity) (div_pos hε₆ (mul_pos (by norm_num) (hC 6))))
  let T : Finset ℝ := insert τ (s.image (fun j ↦ margin j / (2 * C (order j))))
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  let δ := T.min' hT
  have hδ : 0 < δ := by
    have hp : ∀ t ∈ T, 0 < t := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hτ
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
        exact div_pos (hmargin j hj) (mul_pos (by norm_num) (hC (order j)))
    exact hp _ (T.min'_mem hT)
  have hδτ : δ ≤ τ := T.min'_le _ (Finset.mem_insert_self _ _)
  have hδσ₀ : δ ≤ σ₀ := hδτ.trans (min_le_left _ _)
  have hδcap : δ < cap := by
    have hh := hδτ.trans ((min_le_right _ _).trans (min_le_left _ _))
    change δ ≤ cap / 2 at hh
    linarith
  have hscale {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) δ) : σ ∈ Ioc (0 : ℝ) σ₀ :=
    ⟨hσ.1, hσ.2.trans hδσ₀⟩
  refine ⟨U, hU, hKU, δ, hδ, hδcap, hδσ₀.trans hσ₁, ?_, ?_, ?_⟩
  · intro σ hσ
    exact hseg σ ⟨hσ.1, hσ.2.trans hδσ₀⟩
  · intro σ hσ
    obtain ⟨hF, hi, hr, ha⟩ := hgeom σ (hscale hσ)
    refine ⟨hF, hi, hr, ha, ?_, ?_⟩
    · intro j hj
      have hsmall : C (order j) * σ < margin j := by
        have hh : σ ≤ margin j / (2 * C (order j)) := hσ.2.trans
          (T.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩)))
        have := (le_div_iff₀ (show 0 < 2 * C (order j) from mul_pos (by norm_num) (hC (order j)))).mp hh
        have := hmargin j hj
        nlinarith
      exact (hbound (order j) σ (hscale hσ)).1.trans_lt hsmall
    · intro i
      have hsmall : C 6 * σ < ε₆ := by
        have hh : σ ≤ ε₆ / (2 * C 6) := hσ.2.trans
          (hδτ.trans ((min_le_right _ _).trans (min_le_right _ _)))
        have := (le_div_iff₀ (show 0 < 2 * C 6 from mul_pos (by norm_num) (hC 6))).mp hh
        nlinarith
      exact ((hbound 6 σ (hscale hσ)).2 i).trans_lt hsmall
  · intro m
    exact ⟨C m, hC m, fun σ hσ ↦ hbound m σ (hscale hσ)⟩


/-- One common positive source scale meets every fixed finite coefficient
margin, the requested C6 frame tolerance, and a preassigned positive cap
(`main:prop:seed`). The reference is literally `sourceDilation G.map σ` in
every conclusion; no new map or geometric frame is introduced. For consumers
that need to intersect further thresholds, use the preceding interval theorem. -/
theorem exists_source_scale_fullReducedCoefficients_lt
    (G : FlatReference n) {K : Set (Euclidean n)} (hK : IsCompact K)
    {ι : Type*} (s : Finset ι) (order : ι → ℕ) (margin : ι → ℝ)
    (hmargin : ∀ j ∈ s, 0 < margin j) {ε₆ cap : ℝ} (hε₆ : 0 < ε₆) (hcap : 0 < cap) :
    ∃ σ : ℝ, 0 < σ ∧ σ < cap ∧ σ ≤ 1 ∧
      ∃ U : Set (Euclidean n), IsOpen U ∧ K ⊆ U ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ U, t • (σ • x) ∈ G.domain.chart n) ∧
        ContDiff ℝ ∞ (sourceDilation G.map σ) ∧
        IsImmersionOn (sourceDilation G.map σ) U ∧
        HasFullNormalRankOn (sourceDilation G.map σ) U ∧
        ContDiffOn ℝ ∞ (geometricReducedCoefficients (sourceDilation G.map σ)) U ∧
        (∀ j ∈ s, cNorm K (order j)
          (geometricReducedCoefficients (sourceDilation G.map σ) -
            reducedCoefficientBackground (fun _ _ ↦ 0)) < margin j) ∧
        (∀ i, cNorm K 6 (fun x ↦ projectedStress (sourceDilation G.map σ) x i -
          cubeStress n i) < ε₆) ∧
        ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧
          cNorm K m (geometricReducedCoefficients (sourceDilation G.map σ) -
            reducedCoefficientBackground (fun _ _ ↦ 0)) ≤ C * σ ∧
          ∀ i, cNorm K m (fun x ↦ projectedStress (sourceDilation G.map σ) x i -
            cubeStress n i) ≤ C * σ := by
  obtain ⟨U, hU, hKU, δ, hδ, hδcap, hδ₁, hseg, hgeom, hb⟩ :=
    exists_fullReducedCoefficients_finite_margin_interval G hK s order margin hmargin hε₆ hcap
  obtain ⟨hF, hi, hr, ha, hmargin', hframe⟩ := hgeom δ ⟨hδ, le_rfl⟩
  refine ⟨δ, hδ, hδcap, hδ₁, U, hU, hKU, hseg δ ⟨hδ.le, le_rfl⟩,
    hF, hi, hr, ha, hmargin', hframe, ?_⟩
  intro m
  obtain ⟨C, hC, hbC⟩ := hb m
  exact ⟨C, hC, hbC δ ⟨hδ, le_rfl⟩⟩

end JanetCartan.ReferenceInitialization.FullCoefficientDilation
