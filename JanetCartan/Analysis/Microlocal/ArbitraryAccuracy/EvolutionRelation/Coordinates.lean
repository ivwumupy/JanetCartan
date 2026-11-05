module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Geometry.Differential
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.TimeSpace

/-!
# Physical coordinates for the elapsed canonical relation

The recombination map uses the existing Euclidean time/space split and its
literal physical pairing. Consumer: the differential and flow identities in
`ArbitraryAccuracy.EvolutionRelation` (`app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace JanetCartan.ArbitraryAccuracy
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ}

/-- Recombination of the literal time and spatial coordinates, as a continuous
linear map (`app:ch_regular:eq:joint-stationary`). -/
def timeSpacePointCLM : (ℝ × Euclidean d) →L[ℝ] Euclidean (d + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p ↦ timeSpacePoint p.1 p.2
      map_add' := by
        intros
        apply timeSpaceMeasurableEquiv.injective
        simp only [timeSpaceMeasurableEquiv_apply, ← spatialPartCLM_apply, map_add]
        simp [spatialPartCLM_apply]
      map_smul' := by
        intros
        apply timeSpaceMeasurableEquiv.injective
        simp only [timeSpaceMeasurableEquiv_apply, ← spatialPartCLM_apply, map_smul]
        simp [spatialPartCLM_apply] }

/-- The continuous map uses the existing physical coordinates
(`app:ch_regular:eq:joint-stationary`). -/
@[simp] theorem timeSpacePointCLM_apply (p : ℝ × Euclidean d) :
    timeSpacePointCLM p = timeSpacePoint p.1 p.2 := rfl

/-- Recombination recovers the original physical vector
(`app:ch_regular:eq:joint-stationary`). -/
@[simp] theorem timeSpacePoint_coordinates (x : Euclidean (d + 1)) :
    timeSpacePoint (x 0) (spatialPart x) = x :=
  timeSpaceMeasurableEquiv.symm_apply_apply x

end JanetCartan.ArbitraryAccuracy
