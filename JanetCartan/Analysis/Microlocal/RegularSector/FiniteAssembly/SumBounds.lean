module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoordinateSobolev

/-!
# Summing the already transported physical PDO estimates

The algebraic and endpoint constructors export estimates in original physical
coordinates. Feed those exact estimates back through the same isometry to the
existing finite-sum theorem. This does not alter an operator or a norm.
Consumers: `exists_finite_algebraic_pdo_sums` and the selected endpoint sum
(`energy-complete-residual`, `measured-adjoint`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.RegularSector.FiniteAssembly
open FiniteEvolution Characteristic.EvolutionIntegral Pseudodifferential
variable {d q : ℕ} {ι : Type*} [Fintype ι]
local notation "H" => SpacetimeL2 d q

/-- Finite summation from estimates on the actual ORIGINAL-coordinate
operators, including their literal adjoints. This adapts the existing sum
proof to the algebraic and endpoint producers (`measured-adjoint`). -/
theorem finitePhysicalOperator_bound_from_physical
    (index : ι → Fin (d+1)) (T : ι → H →L[ℂ] H)
    (s t high : ℝ) (cost : ι → ℝ)
    (hT : ∀ p, ∀ V : H →L[ℂ] H,
      (V = physicalOperator (index p) (T p) ∨ V = (physicalOperator (index p) (T p)).adjoint) →
      ∀ u, MemVectorFourierSobolev s u →
        MemVectorFourierSobolev t (V u) ∧
        vectorFourierSobolevNorm t (V u) ≤ cost p * (vectorFourierSobolevNorm s u+high*‖u‖))
    (V : H →L[ℂ] H)
    (hV : V = finitePhysicalOperator index T ∨ V = (finitePhysicalOperator index T).adjoint)
    (u : H) (hu : MemVectorFourierSobolev s u) :
    MemVectorFourierSobolev t (V u) ∧
      vectorFourierSobolevNorm t (V u) ≤
        (∑ p, cost p) * (vectorFourierSobolevNorm s u+high*‖u‖) := by
  have hchart p (W : H →L[ℂ] H) (hW : W = T p ∨ W = (T p).adjoint)
      (v : H) (hv : MemVectorFourierSobolev s v) :
      MemVectorFourierSobolev t (W v) ∧
      vectorFourierSobolevNorm t (W v) ≤ cost p * (vectorFourierSobolevNorm s v+high*‖v‖) := by
    have hw : physicalOperator (index p) W = physicalOperator (index p) (T p) ∨
        physicalOperator (index p) W = (physicalOperator (index p) (T p)).adjoint := by
      rcases hW with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (physicalOperator_adjoint _ _).symm
    have hb := hT p _ hw ((physicalPullbackL2 (index p)).symm v)
      ((memVectorFourierSobolev_physicalPullbackL2_symm _ _ _).mpr hv)
    simpa only [physicalOperator_apply, LinearIsometryEquiv.apply_symm_apply,
      memVectorFourierSobolev_physicalPullbackL2_symm,
      vectorFourierSobolevNorm_physicalPullbackL2_symm, LinearIsometryEquiv.norm_map] using hb
  rcases hV with rfl | rfl
  · simpa only [Finset.sum_mul] using finitePhysicalOperator_sobolev_bound
      index T s t cost (fun _ ↦ high) (fun p ↦ hchart p _ (Or.inl rfl)) u hu
  · rw [finitePhysicalOperator_adjoint]
    simpa only [Finset.sum_mul] using finitePhysicalOperator_sobolev_bound
      index (fun p ↦ (T p).adjoint) s t cost (fun _ ↦ high)
      (fun p ↦ hchart p _ (Or.inr rfl)) u hu

end JanetCartan.RegularSector.FiniteAssembly
