module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.NeighborhoodConstruction.FlowIdentities
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Orthogonal physical coordinates for the full phase charts

The adapted coordinates of `app:ch_seed:prop:seed-phase-charts` use the actual
normal and section retained by the frozen Hamilton construction. The map below
is an isometry for the Hilbert spacetime norm. Its zero-energy extension is a
contraction for the product norms used by the quantitative phase producer.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace

namespace JanetCartan.FullPhaseCharts
open ActualCarriers.FrozenPhaseReference

/-- Reassemble the two spectator coordinates and the distinguished incidence
coordinate, shared by the concrete comparison and transversality proofs
(`app:ch_seed:prop:seed-phase-charts`). -/
def carrierParameters : (Euclidean 2 × ℝ) →L[ℝ] Euclidean 3 :=
  LinearMap.toContinuousLinearMap {
    toFun := fun q ↦ WithLp.toLp 2 ![q.2, q.1 0, q.1 1]
    map_add' := by intro p q; ext i; fin_cases i <;> rfl
    map_smul' := by intro c q; ext i; fin_cases i <;> rfl }

@[simp] theorem carrierParameters_apply (q : Euclidean 2 × ℝ) :
    carrierParameters q = WithLp.toLp 2 ![q.2, q.1 0, q.1 1] := rfl

variable {n : ℕ} {ξ : Euclidean n} (a : AdaptedSection ξ)

/-- The literal orthogonal adapted physical coordinates `(t,y) ↦ tν + j y`
of `app:ch_seed:prop:seed-phase-charts`. -/
def adaptedSpacetime : WithLp 2 (ℝ × Euclidean (n - 1)) →ₗᵢ[ℝ] Euclidean n where
  toLinearMap :=
    (HamiltonPhase.flowDifferential a.normal a.embedding.toContinuousLinearMap).toLinearMap.comp
      (WithLp.linearEquiv 2 ℝ (ℝ × Euclidean (n - 1))).toLinearMap
  norm_map' x := by
    change ‖x.ofLp.1 • a.normal + a.embedding x.ofLp.2‖ = ‖x‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq]
    have ho : ⟪a.embedding x.ofLp.2, a.normal⟫_ℝ = 0 := by
      rw [real_inner_comm, a.orthogonal]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      a.orthogonal, ho, real_inner_self_eq_norm_sq, a.normal_unit,
      a.embedding.norm_map, WithLp.prod_inner_apply, mul_zero, zero_add, add_zero,
      one_pow, mul_one, conj_trivial, Real.norm_eq_abs, sq_abs]
    ring

@[simp] theorem adaptedSpacetime_apply (x : WithLp 2 (ℝ × Euclidean (n - 1))) :
    adaptedSpacetime a x = x.ofLp.1 • a.normal + a.embedding x.ofLp.2 := rfl

/-- The section's spanning property proves that the adapted physical map
covers all physical space (`app:ch_seed:prop:seed-phase-charts`). -/
theorem adaptedSpacetime_surjective : Function.Surjective (adaptedSpacetime a) := by
  intro x
  exact ⟨WithLp.toLp 2 (⟪a.normal, x⟫_ℝ, a.embedding.toContinuousLinearMap.adjoint x),
    a.covector_decomposition x⟩

/-- The zero-energy coordinate inclusion used to restrict the SAME current
Hamilton chart in `app:ch_seed:eq:seed-exact-phase-quotient`. -/
def adaptedPhaseInclusion :
    (WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)) →L[ℝ]
      (Euclidean n × (ℝ × Euclidean (n - 1))) :=
  ((adaptedSpacetime a).toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((0 : _ →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ _ _))

@[simp] theorem adaptedPhaseInclusion_apply
    (q : WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)) :
    adaptedPhaseInclusion a q = (adaptedSpacetime a q.1, (0, q.2)) := rfl

/-- The physical/covector restriction loses no derivative and has operator
norm at most one (`app:ch_seed:eq:seed-phase-tame`). -/
theorem norm_adaptedPhaseInclusion_le : ‖adaptedPhaseInclusion a‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro q
  change ‖(adaptedSpacetime a q.1, ((0 : ℝ), q.2))‖ ≤ 1 * ‖q‖
  simp only [Prod.norm_def, norm_zero, LinearIsometry.norm_map,
    max_eq_right (norm_nonneg _), one_mul, le_refl]

end JanetCartan.FullPhaseCharts
