module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalCoordinates
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.CanonicalLocalizers
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Basic

/-!
# Literal localizer integrals in the selected coordinates

The existing canonical proof mask is exactly `m(e x, e ξ)` for the selected
physical permutation `e`. Its unit Jacobian and dual pairing give covariance
of both quantizations, with the source and target symbols in their original
positions. Consumer: the bounded localizer identities and then the selected
factors in `app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FiniteChain.Graph ProtectedMasks
open RegularSector.Characteristic RegularSector.Characteristic.ResidualCoordinates
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)

/-- The existing canonical symbol uses the actual physical permutation on
both base and covector (`app:ch_regular:lem:finite-chain`). -/
theorem canonicalProofLocalizer_coordinateSplit_apply
    (i : Fin (d + 1)) (m : LocalizerSymbol (d + 1)) (x ξ : E) :
    canonicalProofLocalizer (coordinateSplit i) m (x, ξ) =
      m (physicalCoordinates i x, physicalCoordinates i ξ) := rfl

/-- Right quantization commutes with the selected physical pullback, directly
from the two literal integrals (`app:ch_regular:eq:chain-tail`). -/
theorem rightLocalizer_physicalCoordinates
    (i : Fin (d + 1)) (ρ : ℝ) (m : LocalizerSymbol (d + 1))
    (f : E → Fin q → ℂ) (x : E) :
    rightLocalizer ρ (canonicalProofLocalizer (coordinateSplit i) m)
      (f ∘ physicalCoordinates i) x =
      rightLocalizer ρ m f (physicalCoordinates i x) := by
  have hchange (g : E → Fin q → ℂ) := (measurePreserving_physicalCoordinates i).integral_comp
    (physicalCoordinates i).toHomeomorph.measurableEmbedding g
  unfold rightLocalizer graphOperator
  congr 1
  rw [← hchange (fun ξ ↦ ∫ y,
    graphOscillation (fun x ξ : E ↦ inner ℝ x ξ) (physicalCoordinates i x) y ξ •
      ((m (y, ρ⁻¹ • ξ) : ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ)).mulVec (f y))]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [← hchange (fun y ↦
    graphOscillation (fun x ξ : E ↦ inner ℝ x ξ) (physicalCoordinates i x) y
      (physicalCoordinates i ξ) •
      ((m (y, ρ⁻¹ • physicalCoordinates i ξ) : ℂ) •
        (1 : Matrix (Fin q) (Fin q) ℂ)).mulVec (f y))]
  simp only [canonicalProofLocalizer_coordinateSplit_apply, map_smul,
    graphOscillation, physicalCoordinates_inner, Function.comp_apply]

/-- Left quantization keeps the output base under the same physical change
of variables (`app:ch_regular:eq:chain-tail`). -/
theorem leftLocalizer_physicalCoordinates
    (i : Fin (d + 1)) (ρ : ℝ) (m : LocalizerSymbol (d + 1))
    (f : E → Fin q → ℂ) (x : E) :
    leftLocalizer ρ (canonicalProofLocalizer (coordinateSplit i) m)
      (f ∘ physicalCoordinates i) x =
      leftLocalizer ρ m f (physicalCoordinates i x) := by
  have hchange (g : E → Fin q → ℂ) := (measurePreserving_physicalCoordinates i).integral_comp
    (physicalCoordinates i).toHomeomorph.measurableEmbedding g
  unfold leftLocalizer graphOperator
  congr 1
  rw [← hchange (fun ξ ↦ ∫ y,
    graphOscillation (fun x ξ : E ↦ inner ℝ x ξ) (physicalCoordinates i x) y ξ •
      ((m (physicalCoordinates i x, ρ⁻¹ • ξ) : ℂ) •
        (1 : Matrix (Fin q) (Fin q) ℂ)).mulVec (f y))]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [← hchange (fun y ↦
    graphOscillation (fun x ξ : E ↦ inner ℝ x ξ) (physicalCoordinates i x) y
      (physicalCoordinates i ξ) •
      ((m (physicalCoordinates i x, ρ⁻¹ • physicalCoordinates i ξ) : ℂ) •
        (1 : Matrix (Fin q) (Fin q) ℂ)).mulVec (f y))]
  simp only [canonicalProofLocalizer_coordinateSplit_apply, map_smul,
    graphOscillation, physicalCoordinates_inner, Function.comp_apply]

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
