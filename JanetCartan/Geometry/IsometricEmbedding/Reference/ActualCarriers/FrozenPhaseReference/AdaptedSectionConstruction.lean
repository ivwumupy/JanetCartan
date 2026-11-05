module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.Neighborhood
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Adapted orthogonal sections at frozen carrier seeds

The regularity theorem for the seeds of `app:ch_seed:prop:seed-frozen-menu`
provides a transverse direction. Orienting and normalizing it, and choosing an
orthonormal basis of its orthogonal complement, gives the section required by
`LocalFrozenReference` in Step 1 of `app:ch_seed:prop:seed-actual-menu`.
-/

@[expose] public noncomputable section

namespace JanetCartan.ActualCarriers.FrozenPhaseReference

open FrozenMenu
open scoped InnerProductSpace

/-- A frozen carrier seed admits an oriented unit normal and an isometric
parameterization of its entire orthogonal hyperplane. The determinant derivative
in that normal direction is strictly positive. This supplies the adapted section
input to `LocalFrozenReference` (`app:ch_seed:prop:seed-actual-menu`, Step 1),
using seed regularity from `app:ch_seed:prop:seed-frozen-menu`. -/
theorem exists_adaptedSection_of_carrierSeed {n : ℕ} (hn : 5 ≤ n)
    {k s ξ : Euclidean n} (h : CarrierSeed k s ξ) : Nonempty (AdaptedSection ξ) := by
  have hreg := CubeCarrier.regular_of_quadratic_reciprocal_ne_zero
    h.coordinates_ne_zero h.characteristic h.normal_ne_zero
  obtain ⟨v, hv⟩ : ∃ v : Euclidean n, fderiv ℝ cubeDeterminant ξ v ≠ 0 := by
    by_contra! hz
    apply hreg
    ext v
    exact hz v
  obtain ⟨v, hv⟩ : ∃ v : Euclidean n, 0 < fderiv ℝ cubeDeterminant ξ v := by
    rcases lt_or_gt_of_ne hv with hneg | hpos
    · exact ⟨-v, by simpa using neg_pos.mpr hneg⟩
    · exact ⟨v, hpos⟩
  have hv0 : v ≠ 0 := by
    intro heq
    simp [heq] at hv
  let ν := NormedSpace.normalize v
  have hν : ‖ν‖ = 1 := NormedSpace.norm_normalize hv0
  have hν0 : ν ≠ 0 := by
    intro heq
    simp [heq] at hν
  have hpos : 0 < fderiv ℝ cubeDeterminant ξ ν := by
    dsimp [ν, NormedSpace.normalize]
    rw [map_smul, smul_eq_mul]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hv0)) hv
  let : Fact (Module.finrank ℝ (Euclidean n) = (n - 1) + 1) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (n - 1) hν0
  let e : Euclidean (n - 1) →ₗᵢ[ℝ] Euclidean n :=
    (ℝ ∙ ν)ᗮ.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  refine ⟨⟨ν, e, hν, ?_, ?_, hpos⟩⟩
  · intro u
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b.repr.symm u).property
  · intro x hx
    let y : (ℝ ∙ ν)ᗮ := ⟨x, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hx⟩
    refine ⟨b.repr y, ?_⟩
    change ↑(b.repr.symm (b.repr y)) = x
    simp [y]

end JanetCartan.ActualCarriers.FrozenPhaseReference
