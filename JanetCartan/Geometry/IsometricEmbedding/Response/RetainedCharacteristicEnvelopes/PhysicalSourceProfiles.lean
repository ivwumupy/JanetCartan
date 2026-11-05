module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.SourceProfiles
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoordinateSobolev.Fourier

/-!
# The literal source Fourier words in the selected physical coordinates

The selected physical permutation preserves Lebesgue measure and every signed
Fourier--Sobolev norm. It acts only on the spatial argument of the source,
leaving all independent parameter directions and the cubic source size intact.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
open Pseudodifferential RegularSector.FiniteEvolution
open RegularSector.Characteristic.ResidualCoordinates
variable {d r : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- The original full-parameter word in selected physical coordinates has
exactly the original Fourier--Sobolev norm, with the original Lebesgue measure.
The independent covector is untouched, so no parameter-direction constant or
frequency loss is introduced. Consumer: the source input to
`fullSource_physical_incidence_solver_residual_envelopes`
(`app:ch_response:eq:response-graded-reduced`). -/
theorem fullSource_parameterWord_fourier_physicalPullback
    (index : Fin (d+1)) (a : E × Par → F) (c : Par) (k : ℕ) (v : Fin k → Par)
    (hm : MemLp (fun y ↦ iteratedFDeriv ℝ k (fun q ↦ a (y,q)) c v) 2 volume)
    (s : ℝ) :
    let f := fun y ↦ iteratedFDeriv ℝ k (fun q ↦ a (y,q)) c v
    let g := fun y ↦ iteratedFDeriv ℝ k (fun q ↦ a (physicalCoordinates index y,q)) c v
    ∃ hg : MemLp g 2 volume,
      hg.toLp g = physicalPullbackL2 index (hm.toLp f) ∧
      (MemVectorFourierSobolev s (hg.toLp g) ↔ MemVectorFourierSobolev s (hm.toLp f)) ∧
      vectorFourierSobolevNorm s (hg.toLp g) = vectorFourierSobolevNorm s (hm.toLp f) := by
  intro f g
  let hg : MemLp g 2 volume := hm.comp_measurePreserving (measurePreserving_physicalCoordinates index)
  have he : hg.toLp g = physicalPullbackL2 index (hm.toLp f) := rfl
  exact ⟨hg,he,he ▸ memVectorFourierSobolev_physicalPullbackL2 index s (hm.toLp f),
    he ▸ vectorFourierSobolevNorm_physicalPullbackL2 index s (hm.toLp f)⟩

end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
