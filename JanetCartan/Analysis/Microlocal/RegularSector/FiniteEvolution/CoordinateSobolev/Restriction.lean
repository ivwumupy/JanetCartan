module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoordinateSobolev.Estimates
public import JanetCartan.Analysis.Sobolev.Local.Fourier
public import JanetCartan.Analysis.Sobolev.Local.Cutoff
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization.RestrictionBounds

/-!
# Genuine restriction norms for the physical coordinate estimates

Positive Fourier output regularity constructs actual weak Sobolev extensions
using `Local.Fourier`, and measurement cutoffs use `Local.Cutoff`. Fourier and
restriction norms are related by proved constants, never identified. For higher
orders the source is required to have its stated Fourier regularity after zero
extension; arbitrary positive-order zero extension is not asserted. At the
L² → H¹ endpoint this premise is automatic on every `LocalL2` input, in both
orientations of the existing localized operator.
Sources: `sector-theorem-residual`, `measured-adjoint`, `finite-gap-theorem`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set
open scoped NNReal ENNReal
namespace JanetCartan.RegularSector.FiniteEvolution
open Characteristic.EvolutionIntegral Characteristic.RetardedLocalization
open Pseudodifferential LocalSobolev
variable {d q : ℕ}
local notation "Dom" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d q
local notation "Fiber" => EuclideanSpace ℂ (Fin q)
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- A dimension-only comparison converts the physical operator's positive
output into the genuine restriction norm of the existing local operator.
The source Fourier premise is explicit (`sector-theorem-residual`). -/
theorem exists_physicalOperator_restriction_constant (d q s : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (i : Fin (d+1)) (T : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
      (t C K : ℝ),
      (∀ u, MemVectorFourierSobolev t u →
        MemVectorFourierSobolev (s : ℝ) (T u) ∧
        vectorFourierSobolevNorm (s : ℝ) (T u) ≤ C * (vectorFourierSobolevNorm t u + K * ‖u‖)) →
      ∀ (U W : Set (Euclidean (d+1))) (hU : MeasurableSet U)
        (u : LocalL2 U (EuclideanSpace ℂ (Fin q))),
        MemVectorFourierSobolev t (SmallSupport.zeroExtend hU u) →
        MemRestrictionSobolev W s (localRetardedOperator hU W (physicalOperator i T) u) ∧
        restrictionSobolevNorm W s (localRetardedOperator hU W (physicalOperator i T) u) ≤
          (D * C) * (vectorFourierSobolevNorm t (SmallSupport.zeroExtend hU u) + K * ‖u‖) := by
  obtain ⟨D, hD, hconvert⟩ := vector_restrictionSobolev_nat_bounds (d+1) q s
  refine ⟨D, hD, ?_⟩
  intro i T t C K hT U W hU u hu
  obtain ⟨hm, hb⟩ := physicalOperator_sobolev_bound i T t s C K hT
    (SmallSupport.zeroExtend hU u) hu
  obtain ⟨hlocal, hn⟩ := hconvert _ hm W
    (localRetardedOperator hU W (physicalOperator i T) u)
    (restrictL2_coeFn W _).symm
  refine ⟨hlocal, hn.trans ?_⟩
  simpa only [LinearIsometry.norm_map, mul_assoc] using mul_le_mul_of_nonneg_left hb hD.le

/-- The same comparison for the finite physical sum, allowing each chart's
own profile. Its constants precede all varying operators and input data
(`energy-complete-residual`). -/
theorem exists_finitePhysicalOperator_restriction_constant (d q s : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ {ι : Type*} [Fintype ι]
      (index : ι → Fin (d+1)) (T : ι → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
      (t : ℝ) (C K : ι → ℝ),
      (∀ p u, MemVectorFourierSobolev t u →
        MemVectorFourierSobolev (s : ℝ) (T p u) ∧
        vectorFourierSobolevNorm (s : ℝ) (T p u) ≤ C p *
          (vectorFourierSobolevNorm t u + K p * ‖u‖)) →
      ∀ (U W : Set (Euclidean (d+1))) (hU : MeasurableSet U)
        (u : LocalL2 U (EuclideanSpace ℂ (Fin q))),
        MemVectorFourierSobolev t (SmallSupport.zeroExtend hU u) →
        MemRestrictionSobolev W s (localRetardedOperator hU W (finitePhysicalOperator index T) u) ∧
        restrictionSobolevNorm W s (localRetardedOperator hU W (finitePhysicalOperator index T) u) ≤
          D * ∑ p, C p * (vectorFourierSobolevNorm t (SmallSupport.zeroExtend hU u) + K p * ‖u‖) := by
  obtain ⟨D, hD, hconvert⟩ := vector_restrictionSobolev_nat_bounds (d+1) q s
  refine ⟨D, hD, ?_⟩
  intro ι _ index T t C K hT U W hU u hu
  obtain ⟨hm, hb⟩ := finitePhysicalOperator_sobolev_bound index T t s C K hT
    (SmallSupport.zeroExtend hU u) hu
  obtain ⟨hlocal, hn⟩ := hconvert _ hm W
    (localRetardedOperator hU W (finitePhysicalOperator index T) u)
    (restrictL2_coeFn W _).symm
  refine ⟨hlocal, hn.trans ?_⟩
  simpa only [LinearIsometry.norm_map] using mul_le_mul_of_nonneg_left hb hD.le

/-- The existing measurement bump has its genuine restriction Sobolev bound
on the physical local output, obtained by the proved cutoff API. No Fourier
norm is silently substituted for a local norm (`measured-adjoint`). -/
theorem exists_measured_physicalOperator_restriction_constant
    (x : Dom) (χ : ContDiffBump x) (s : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (i : Fin (d+1)) (T : H →L[ℂ] H) (t C K : ℝ),
      (∀ u, MemVectorFourierSobolev t u →
        MemVectorFourierSobolev (s : ℝ) (T u) ∧
        vectorFourierSobolevNorm (s : ℝ) (T u) ≤ C * (vectorFourierSobolevNorm t u + K * ‖u‖)) →
      ∀ (U W : Set Dom) (hU : MeasurableSet U) (_hW : MeasurableSet W),
        tsupport (χ : Dom → ℝ) ⊆ W → ∀ (u : LocalL2 U Fiber),
        MemVectorFourierSobolev t (SmallSupport.zeroExtend hU u) →
        let v := SmallSupport.bumpL2 (p := 2) le_rfl χ
          (localRetardedOperator hU W (physicalOperator i T) u)
        MemRestrictionSobolev W s v ∧ restrictionSobolevNorm W s v ≤
          (D * C) * (vectorFourierSobolevNorm t (SmallSupport.zeroExtend hU u) + K * ‖u‖) := by
  obtain ⟨D, hD, hlocal⟩ := exists_physicalOperator_restriction_constant d q s
  obtain ⟨B, hB, hcut⟩ := exists_bumpL2_sobolev_bound (F := Fiber) χ s
  refine ⟨B * D, mul_pos (lt_of_lt_of_le zero_lt_one hB) hD, ?_⟩
  intro i T t C K hT U W hU hW hs u hu
  obtain ⟨hm, hn⟩ := hlocal i T t C K hT U W hU u hu
  obtain ⟨hcm, hcn⟩ := hcut W hW hs _ hm
  refine ⟨hcm, hcn.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hn (zero_le_one.trans hB)

/-- Both domain orientations of the physical gain-one map give the fixed
inverse's genuine LocalL2 → restriction-H¹ input, with the original profile
and fixed shift (`finite-gap-theorem`, `measured-adjoint`). -/
theorem exists_physicalOperator_local_H1_constant (d q : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (i : Fin (d+1)) (T : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
      (μ : ℕ) (C K : ℕ → ℝ),
      (∀ s : ℕ, ∀ V : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
        (V = T ∨ V = T.adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-1 : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (V u) ∧
        vectorFourierSobolevNorm (s : ℝ) (V u) ≤ C s *
          (vectorFourierSobolevNorm ((s-1 : ℕ) : ℝ) u + K (s+μ) * ‖u‖)) →
      ∀ (U W : Set (Euclidean (d+1))) (hU : MeasurableSet U) (_hW : MeasurableSet W),
        (∀ u : LocalL2 U (EuclideanSpace ℂ (Fin q)),
          MemRestrictionSobolev W 1 (localRetardedOperator hU W (physicalOperator i T) u) ∧
          restrictionSobolevNorm W 1 (localRetardedOperator hU W (physicalOperator i T) u) ≤
            (D * C 1 * (1 + K (1+μ))) * ‖u‖) ∧
        (∀ v : LocalL2 W (EuclideanSpace ℂ (Fin q)),
          MemRestrictionSobolev U 1 ((localRetardedOperator hU W (physicalOperator i T)).adjoint v) ∧
          restrictionSobolevNorm U 1 ((localRetardedOperator hU W (physicalOperator i T)).adjoint v) ≤
            (D * C 1 * (1 + K (1+μ))) * ‖v‖) := by
  obtain ⟨D, hD, hlocal⟩ := exists_localRetarded_restrictionH1_constant d q
  refine ⟨D, hD, ?_⟩
  intro i T μ C K hT U W hU hW
  simpa only [one_mul] using hlocal (physicalOperator i T) μ 1 C K
    (by simpa only [one_mul] using physicalOperator_positive_integer_bounds i T 1 μ C K hT)
    U W hU hW

/-- The finite physical residual and its literal local adjoint satisfy the
same genuine restriction-H¹ endpoint, with the chart constants summed and
no coefficient shift added (`finite-gap-theorem`, `energy-complete-residual`). -/
theorem exists_finitePhysicalOperator_local_H1_constant (d q : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ {ι : Type*} [Fintype ι]
      (index : ι → Fin (d+1)) (T : ι → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
      (μ : ℕ) (C : ι → ℕ → ℝ) (K : ℕ → ℝ),
      (∀ p, ∀ s : ℕ, ∀ V : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
        (V = T p ∨ V = (T p).adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-1 : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (V u) ∧
        vectorFourierSobolevNorm (s : ℝ) (V u) ≤ C p s *
          (vectorFourierSobolevNorm ((s-1 : ℕ) : ℝ) u + K (s+μ) * ‖u‖)) →
      ∀ (U W : Set (Euclidean (d+1))) (hU : MeasurableSet U) (_hW : MeasurableSet W),
        (∀ u : LocalL2 U (EuclideanSpace ℂ (Fin q)),
          MemRestrictionSobolev W 1 (localRetardedOperator hU W (finitePhysicalOperator index T) u) ∧
          restrictionSobolevNorm W 1 (localRetardedOperator hU W (finitePhysicalOperator index T) u) ≤
            (D * (∑ p, C p 1) * (1 + K (1+μ))) * ‖u‖) ∧
        (∀ v : LocalL2 W (EuclideanSpace ℂ (Fin q)),
          MemRestrictionSobolev U 1 ((localRetardedOperator hU W
            (finitePhysicalOperator index T)).adjoint v) ∧
          restrictionSobolevNorm U 1 ((localRetardedOperator hU W
            (finitePhysicalOperator index T)).adjoint v) ≤
            (D * (∑ p, C p 1) * (1 + K (1+μ))) * ‖v‖) := by
  obtain ⟨D, hD, hlocal⟩ := exists_localRetarded_restrictionH1_constant d q
  refine ⟨D, hD, ?_⟩
  intro ι _ index T μ C K hT U W hU hW
  simpa only [one_mul] using hlocal (finitePhysicalOperator index T) μ 1
    (fun s ↦ ∑ p, C p s) K
    (by simpa only [one_mul] using
      finitePhysicalOperator_positive_integer_bounds index T 1 μ C K hT) U W hU hW

end JanetCartan.RegularSector.FiniteEvolution
