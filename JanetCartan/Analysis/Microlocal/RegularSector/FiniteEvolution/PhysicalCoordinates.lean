module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.Basic
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization.Support
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.CoordinateCollars

/-!
# Literal L² transport of the finite retarded operators

The selected time coordinate acts on independent variables only. Transport the
actual Lebesgue L² classes by its volume-preserving permutation, keep both
physical masks, and reverse exactly the same conjugation for the adjoint.
This supplies the common physical space for finite summation; it does not
assert the remaining complete PDE residual identity or a Sobolev estimate.
Source: `app:ch_regular_base:eq:energy-complete-residual` and
`app:ch_regular_base:eq:measured-adjoint`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.FiniteEvolution
open Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open FourierIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d q

/-- The existing physical permutation as an isometry. Fiber coordinates are
unchanged (`app:ch_regular_base:eq:energy-complete-residual`). -/
def physicalCoordinateIsometry (i : Fin (d+1)) : E ≃ₗᵢ[ℝ] E where
  __ := (physicalCoordinates i).toLinearEquiv
  norm_map' := FiniteMasks.ActualFamily.norm_physicalCoordinates i

/-- Pull actual original physical L² data into the time-zero chart. This is
an isometric equivalence for the same Euclidean Lebesgue measure, with no
change in the physical Fourier normalization (`fixed-time-representation`). -/
def physicalPullbackL2 (i : Fin (d+1)) : H ≃ₗᵢ[ℂ] H where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (physicalCoordinates i)
    (measurePreserving_physicalCoordinates i)
  invFun := Lp.compMeasurePreserving (physicalCoordinates i).symm
    ((measurePreserving_physicalCoordinates i).symm
      (physicalCoordinates i).toHomeomorph.toMeasurableEquiv)
  left_inv u := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ u) = u
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [ContinuousLinearEquiv.self_comp_symm] using Lp.compMeasurePreserving_id_apply u
  right_inv u := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ u) = u
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [ContinuousLinearEquiv.symm_comp_self] using Lp.compMeasurePreserving_id_apply u

/-- The pullback acts on literal representatives (`fixed-time-representation`). -/
theorem physicalPullbackL2_coeFn (i : Fin (d+1)) (u : H) :
    physicalPullbackL2 i u =ᵐ[volume] u ∘ physicalCoordinates i :=
  Lp.coeFn_compMeasurePreserving _ _

/-- The inverse pullback acts on the same representatives
(`app:ch_regular_base:eq:measured-adjoint`). -/
theorem physicalPullbackL2_symm_coeFn (i : Fin (d+1)) (u : H) :
    (physicalPullbackL2 i).symm u =ᵐ[volume] u ∘ (physicalCoordinates i).symm :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Pull back compact smooth physical tests through the selected permutation.
The same source mask can then act before Fourier multiplication
(`app:ch_regular_base:eq:fixed-time-representation`). -/
def physicalPullbackTest (i : Fin (d+1)) (u : graphTestSpace (d+1) q) :
    graphTestSpace (d+1) q :=
  ⟨u.val ∘ physicalCoordinates i, u.property.1.comp (physicalCoordinates i).contDiff,
    ((physicalCoordinates i).toHomeomorph.isCompact_preimage.mpr u.property.2).of_isClosed_subset
      (isClosed_tsupport _) (tsupport_comp_subset_preimage _ (physicalCoordinates i).continuous)⟩

/-- Test inclusion commutes with the actual physical L² pullback
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem physicalPullbackL2_graphTestToLp (i : Fin (d+1)) (u : graphTestSpace (d+1) q) :
    physicalPullbackL2 i (graphTestToLp u) = graphTestToLp (physicalPullbackTest i u) := by
  apply Lp.ext
  have hu := (measurePreserving_physicalCoordinates i).quasiMeasurePreserving.ae_eq_comp
    (graphTest_memLp u).coeFn_toLp
  exact (physicalPullbackL2_coeFn i _).trans
    (hu.trans (graphTest_memLp (physicalPullbackTest i u)).coeFn_toLp.symm)

/-- The constructed chart operator in original physical coordinates
(`app:ch_regular_base:eq:energy-complete-residual`). -/
def physicalOperator (i : Fin (d+1)) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (physicalPullbackL2 i).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp (physicalPullbackL2 i).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Exact action of physical conjugation, with the original input first
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem physicalOperator_apply (i : Fin (d+1)) (T : H →L[ℂ] H) (u : H) :
    physicalOperator i T u = (physicalPullbackL2 i).symm (T (physicalPullbackL2 i u)) := rfl

/-- Physical conjugation commutes with the literal Hilbert adjoint; the
source and output roles are reversed, without replacing the adjoint
(`app:ch_regular_base:eq:measured-adjoint`). -/
theorem physicalOperator_adjoint (i : Fin (d+1)) (T : H →L[ℂ] H) :
    (physicalOperator i T).adjoint = physicalOperator i T.adjoint := by
  unfold physicalOperator
  simp only [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm,
    LinearIsometryEquiv.symm_symm, ContinuousLinearMap.comp_assoc]

/-- The physical coordinate change introduces no L² loss
(`app:ch_regular_base:eq:sector-theorem-solution`). -/
theorem norm_physicalOperator_le (i : Fin (d+1)) (T : H →L[ℂ] H) :
    ‖physicalOperator i T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  simpa only [physicalOperator_apply, LinearIsometryEquiv.norm_map] using
    T.le_opNorm (physicalPullbackL2 i u)

/-- The literal test formula of a constructed chart operator transfers to
original physical coordinates by the same permutation on its input and
output. In particular the Fourier cutoff is never commuted through the
source multiplication (`fixed-time-representation`). -/
theorem physicalOperator_test_action
    (i : Fin (d+1)) (T : H →L[ℂ] H)
    (action : graphTestSpace (d+1) q → E → EuclideanSpace ℂ (Fin q))
    (hT : ∀ u, T (graphTestToLp u) =ᵐ[volume] action u)
    (u : graphTestSpace (d+1) q) :
    physicalOperator i T (graphTestToLp u) =ᵐ[volume]
      action (physicalPullbackTest i u) ∘ (physicalCoordinates i).symm := by
  rw [physicalOperator_apply, physicalPullbackL2_graphTestToLp]
  exact (physicalPullbackL2_symm_coeFn i _).trans
    (((measurePreserving_physicalCoordinates i).symm
      (physicalCoordinates i).toHomeomorph.toMeasurableEquiv).quasiMeasurePreserving.ae_eq_comp
        (hT (physicalPullbackTest i u)))

/-- Finite physical sum of the SAME chart operators. The complete solver
adds the separately constructed algebraic factors; this definition also
sums the `PW₁` retarded residual factors (`energy-complete-residual`). -/
def finitePhysicalOperator {ι : Type*} [Fintype ι]
    (index : ι → Fin (d+1)) (T : ι → H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ p, physicalOperator (index p) (T p)

/-- The finite physical adjoint is the sum of the literal reversed chart
operators (`app:ch_regular_base:eq:measured-adjoint`). -/
theorem finitePhysicalOperator_adjoint {ι : Type*} [Fintype ι]
    (index : ι → Fin (d+1)) (T : ι → H →L[ℂ] H) :
    (finitePhysicalOperator index T).adjoint =
      finitePhysicalOperator index (fun p ↦ (T p).adjoint) := by
  simp only [finitePhysicalOperator, map_sum, physicalOperator_adjoint]

/-- The actual finite test action is the sum of the original chart test
actions with their own coordinate pullbacks. This preserves each source
mask before its physical Fourier multiplier (`energy-complete-residual`). -/
theorem finitePhysicalOperator_test_action {ι : Type*} [Fintype ι]
    (index : ι → Fin (d+1)) (T : ι → H →L[ℂ] H)
    (action : ι → graphTestSpace (d+1) q → E → EuclideanSpace ℂ (Fin q))
    (hT : ∀ p u, T p (graphTestToLp u) =ᵐ[volume] action p u)
    (u : graphTestSpace (d+1) q) :
    finitePhysicalOperator index T (graphTestToLp u) =ᵐ[volume]
      fun x ↦ ∑ p, action p (physicalPullbackTest (index p) u)
        ((physicalCoordinates (index p)).symm x) := by
  classical
  have hsum := Lp.coeFn_finsetSum Finset.univ
    (fun p ↦ physicalOperator (index p) (T p) (graphTestToLp u))
  have hall := ae_all_iff.mpr fun p ↦ physicalOperator_test_action (index p) (T p)
    (action p) (hT p) u
  simp only [finitePhysicalOperator, sum_apply]
  filter_upwards [hsum, hall] with x hx hp
  simp only [Finset.sum_apply] at hx
  exact hx.trans (Finset.sum_congr rfl fun p _ ↦ hp p)

/-- Finite physical summation retains an input-independent L² constant
(`app:ch_regular_base:eq:sector-theorem-solution`). -/
theorem norm_finitePhysicalOperator_le {ι : Type*} [Fintype ι]
    (index : ι → Fin (d+1)) (T : ι → H →L[ℂ] H) :
    ‖finitePhysicalOperator index T‖ ≤ ∑ p, ‖T p‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ ↦ norm_physicalOperator_le (index p) (T p))

end JanetCartan.RegularSector.FiniteEvolution
