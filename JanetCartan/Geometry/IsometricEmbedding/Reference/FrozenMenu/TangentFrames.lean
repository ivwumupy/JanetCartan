module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.TangentFrames.ProjectionRank
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.TangentFrames.GenericSelection

/-!
# Tangent three-frames for the frozen menu

The simultaneous frame selection in Step 3 of
`app:ch_seed:prop:seed-frozen-menu`. The projection ranks are proved in
`TangentFrames.ProjectionRank`; `TangentFrames.GenericSelection` chooses three
columns avoiding the finitely many bad subspaces. Together with seed
transversality, these give an admissible continuous linear frame.
-/

@[expose] public noncomputable section

namespace JanetCartan.FrozenMenu

/-- Incidence differential restricted to the characteristic tangent space,
as used in `app:ch_seed:prop:seed-frozen-menu`, Step 3. -/
def tangentIncidence {n : ℕ} (k ξ : Euclidean n) : tangentSpace ξ →ₗ[ℝ] ℝ :=
  (fderiv ℝ (incidence k) ξ).toLinearMap.comp (tangentSpace ξ).subtype

/-- Seed transversality makes the incidence functional nonzero on the
characteristic tangent space (`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem CarrierSeed.tangentIncidence_ne_zero {n : ℕ} {k s ξ : Euclidean n}
    (h : CarrierSeed k s ξ) : tangentIncidence k ξ ≠ 0 := by
  obtain ⟨e, he, hi⟩ := h.transverse
  intro hz
  have he' : e ∈ tangentSpace ξ := he
  have hh := LinearMap.congr_fun hz ⟨e, he'⟩
  exact hi hh

/-- Every carrier seed in dimension at least five admits a tangent three-frame
whose first column is transverse to incidence and whose projection to every
bad-space orthogonal complement is injective
(`app:ch_seed:prop:seed-frozen-menu`, Step 3).

Successive avoidance of finitely many proper subspaces implements the
manuscript's simultaneous nonvanishing selection. All rank and incidence
hypotheses are supplied by the seed. -/
theorem CarrierSeed.exists_admissibleFrame {n : ℕ} (hn : 5 ≤ n)
    {k s ξ : Euclidean n} (h : CarrierSeed k s ξ) :
    ∃ A : Euclidean 3 →L[ℝ] Euclidean n, IsAdmissibleFrame k ξ A := by
  classical
  obtain ⟨B, hinc, hproj⟩ := exists_threeFrame_of_rank_ge_three
    (fun L : ↥(cubeBadSubspaces n) ↦ tangentProjection ξ L.val)
    (tangentIncidence k ξ) h.tangentIncidence_ne_zero
    (fun L ↦ h.tangentProjection_rank_ge_three hn L.property)
  let A : Euclidean 3 →L[ℝ] Euclidean n :=
    ((tangentSpace ξ).subtype.comp B).toContinuousLinearMap
  refine ⟨A, ?_, hinc, ?_⟩
  · ext z
    exact (B z).property
  · intro L hL
    exact hproj ⟨L, hL⟩

end JanetCartan.FrozenMenu
