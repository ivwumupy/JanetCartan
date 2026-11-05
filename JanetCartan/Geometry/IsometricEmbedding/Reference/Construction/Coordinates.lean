module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Bending

/-! Coordinate inclusions for Proposition `app:ch_seed:prop:seed-analytic`. -/

@[expose] public noncomputable section

namespace JanetCartan.ReferenceConstruction

/-- Proposition `app:ch_seed:prop:seed-analytic`: append one real normal coordinate. -/
def appendLinearMap (m : ℕ) : WithLp 2 (Euclidean m × ℝ) →ₗ[ℝ] Euclidean (m + 1) where
  toFun z := WithLp.toLp 2 (Fin.lastCases z.ofLp.2 (fun i ↦ z.ofLp.1 i))
  map_add' z w := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  map_smul' c z := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp

/-- Proposition `app:ch_seed:prop:seed-analytic`: appending coordinates preserves inner products. -/
theorem appendLinearMap_inner (m : ℕ) (z w : WithLp 2 (Euclidean m × ℝ)) :
    inner ℝ (appendLinearMap m z) (appendLinearMap m w) = inner ℝ z w := by
  simp only [PiLp.inner_apply, Fin.sum_univ_castSucc, appendLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk, Fin.lastCases_castSucc,
    Fin.lastCases_last, WithLp.prod_inner_apply]

/-- Proposition `app:ch_seed:prop:seed-analytic`: identify the bending target with Euclidean
coordinates. -/
def appendIsometry (m : ℕ) : WithLp 2 (Euclidean m × ℝ) ≃ₗᵢ[ℝ] Euclidean (m + 1) :=
  LinearIsometryEquiv.ofSurjective
    ((appendLinearMap m).isometryOfInner (appendLinearMap_inner m)) (by
      intro y
      refine ⟨WithLp.toLp 2 (WithLp.toLp 2 (fun i ↦ y i.castSucc), y (Fin.last m)), ?_⟩
      change WithLp.toLp 2 (Fin.lastCases (y (Fin.last m)) (fun i ↦ y i.castSucc)) = y
      ext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp)

/-- Proposition `app:ch_seed:prop:seed-analytic`: the old coordinates are unchanged. -/
@[simp] theorem appendIsometry_castSucc (m : ℕ) (z : WithLp 2 (Euclidean m × ℝ))
    (i : Fin m) : appendIsometry m z i.castSucc = z.ofLp.1 i := by
  change (Fin.lastCases z.ofLp.2 (fun j ↦ z.ofLp.1 j) : Fin (m + 1) → ℝ) i.castSucc = _
  simp
/-- Proposition `app:ch_seed:prop:seed-analytic`: the last coordinate is the new normal. -/
@[simp] theorem appendIsometry_last (m : ℕ) (z : WithLp 2 (Euclidean m × ℝ)) :
    appendIsometry m z (Fin.last m) = z.ofLp.2 := by
  change (Fin.lastCases z.ofLp.2 (fun j ↦ z.ofLp.1 j) : Fin (m + 1) → ℝ) (Fin.last m) = _
  simp
end JanetCartan.ReferenceConstruction
