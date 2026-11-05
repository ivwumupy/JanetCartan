module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Positive
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RealPairing

/-!
# The real physical pair preserves the additive tame profile

Transfer the complex restriction estimate to the literal real compression of
`S+cSc`, at arbitrary natural input and output orders. The fixed numerical
constant does not alter the high coefficient profile or the L² low-data term.
Consumers: `sector-theorem-solution`, `sector-theorem-residual` and
`measured-adjoint` for the finite direct construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped JanetCartan.RegularSector.Realization
namespace JanetCartan.RegularSector.FiniteAssembly
open Realization LocalSobolev Characteristic.RetardedLocalization
open JanetCartan.ArbitraryAccuracy.ResidualLocalization
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "RF" => EuclideanSpace ℝ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

/-- The actual plus-paired real compression preserves the two-term tame
estimate at the same input and output orders (`sector-theorem-solution`,
`sector-theorem-residual`). The premise is the complex restriction estimate
produced by `exists_local_sourceCut_restriction_tame_constant` after its
source-absorption premise has been discharged. -/
theorem localRealCompression_physicalPair_restriction_tame_bound
    {U V : Set E} (hU : MeasurableSet U) (T : H →L[ℂ] H) (a b : ℕ)
    (A high : ℝ) (hA : 0 ≤ A) (hhigh : 0 ≤ high)
    (hT : ∀ u : LocalL2 U F, MemRestrictionSobolev U a u →
      MemRestrictionSobolev V b (localRetardedOperator hU V T u) ∧
        restrictionSobolevNorm V b (localRetardedOperator hU V T u) ≤
          A*(restrictionSobolevNorm U a u+high*‖u‖))
    (u : LocalL2 U RF) (hu : MemRestrictionSobolev U a u) :
    MemRestrictionSobolev V b
        (localRealCompression hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) u) ∧
      restrictionSobolevNorm V b
        (localRealCompression hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) u) ≤
          (8*A)*(restrictionSobolevNorm U a u+high*‖u‖) := by
  obtain ⟨hi, hni⟩ := compLp_restrictionSobolev_bound (euclideanComplexInclusion (ι := Fin q)) hu
  change MemRestrictionSobolev U a (l2ComplexInclusion (volume.restrict U) u) at hi
  change restrictionSobolevNorm U a (l2ComplexInclusion (volume.restrict U) u) ≤ _ at hni
  have hni' : restrictionSobolevNorm U a (l2ComplexInclusion (volume.restrict U) u) ≤
      2*restrictionSobolevNorm U a u := hni.trans
    (mul_le_mul_of_nonneg_right (by linarith [euclideanComplexInclusion_norm_le (ι := Fin q)])
      restrictionSobolevNorm_nonneg)
  have hli : ‖l2ComplexInclusion (volume.restrict U) u‖ ≤ ‖u‖ := by
    simpa only [one_mul] using (l2ComplexInclusion (volume.restrict U)).le_of_opNorm_le
      (l2ComplexInclusion_norm_le _) u
  obtain ⟨hm, hn⟩ := hT (l2ComplexInclusion (volume.restrict U) u) hi
  obtain ⟨hr, hnr⟩ := compLp_restrictionSobolev_bound (euclideanRealPart (ι := Fin q)) hm
  change MemRestrictionSobolev V b (localRealCompression hU V T u) at hr
  change restrictionSobolevNorm V b (localRealCompression hU V T u) ≤ _ at hnr
  have hnT : restrictionSobolevNorm V b
      (localRetardedOperator hU V T (l2ComplexInclusion (volume.restrict U) u)) ≤
      (2*A)*(restrictionSobolevNorm U a u+high*‖u‖) := by
    calc
      _ ≤ A*(2*restrictionSobolevNorm U a u+high*‖u‖) :=
        hn.trans (mul_le_mul_of_nonneg_left
          (add_le_add hni' (mul_le_mul_of_nonneg_left hli hhigh)) hA)
      _ ≤ _ := by nlinarith [mul_nonneg hA (mul_nonneg hhigh (norm_nonneg u))]
  have hnR : restrictionSobolevNorm V b (localRealCompression hU V T u) ≤
      (4*A)*(restrictionSobolevNorm U a u+high*‖u‖) := by
    calc
      _ ≤ 2*restrictionSobolevNorm V b
          (localRetardedOperator hU V T (l2ComplexInclusion (volume.restrict U) u)) :=
        hnr.trans (mul_le_mul_of_nonneg_right
          (by linarith [euclideanRealPart_norm_le (ι := Fin q)])
          restrictionSobolevNorm_nonneg)
      _ ≤ 2*((2*A)*(restrictionSobolevNorm U a u+high*‖u‖)) :=
        mul_le_mul_of_nonneg_left hnT (by norm_num)
      _ = _ := by ring
  rw [localRealCompression_physicalPair]
  refine ⟨hr.smul 2, ?_⟩
  rw [restrictionSobolevNorm_smul hr]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

/-- The real physical pair and its literal adjoint keep the same original
coefficient profile, with exchanged source/measurement domains
(`measured-adjoint`, `sector-theorem-residual`). -/
theorem localRealCompression_physicalPair_restriction_tame_bounds
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (T : H →L[ℂ] H) (a b : ℕ) (A high : ℝ) (hA : 0 ≤ A) (hhigh : 0 ≤ high)
    (hf : ∀ u : LocalL2 U F, MemRestrictionSobolev U a u →
      MemRestrictionSobolev V b (localRetardedOperator hU V T u) ∧
        restrictionSobolevNorm V b (localRetardedOperator hU V T u) ≤
          A*(restrictionSobolevNorm U a u+high*‖u‖))
    (ha : ∀ v : LocalL2 V F, MemRestrictionSobolev V a v →
      MemRestrictionSobolev U b ((localRetardedOperator hU V T).adjoint v) ∧
        restrictionSobolevNorm U b ((localRetardedOperator hU V T).adjoint v) ≤
          A*(restrictionSobolevNorm V a v+high*‖v‖)) :
    let R := localRealCompression hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T))
    (∀ u : LocalL2 U RF, MemRestrictionSobolev U a u →
      MemRestrictionSobolev V b (R u) ∧ restrictionSobolevNorm V b (R u) ≤
        (8*A)*(restrictionSobolevNorm U a u+high*‖u‖)) ∧
    (∀ v : LocalL2 V RF, MemRestrictionSobolev V a v →
      MemRestrictionSobolev U b (R.adjoint v) ∧ restrictionSobolevNorm U b (R.adjoint v) ≤
        (8*A)*(restrictionSobolevNorm V a v+high*‖v‖)) := by
  refine ⟨localRealCompression_physicalPair_restriction_tame_bound hU T a b A high hA hhigh hf, ?_⟩
  intro v hv
  rw [localRealCompression_adjoint hU hV, physicalPairedSectorSum_adjoint_eq]
  apply localRealCompression_physicalPair_restriction_tame_bound hV T.adjoint a b A high hA hhigh _ v hv
  simpa only [localRetardedOperator_adjoint hU hV] using ha

end JanetCartan.RegularSector.FiniteAssembly
