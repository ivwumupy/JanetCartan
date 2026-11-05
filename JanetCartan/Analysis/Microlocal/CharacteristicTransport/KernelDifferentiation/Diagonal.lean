module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.KernelDifferentiation.RetardedAction
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.MultiplierSlices

/-! # The diagonal endpoint with the actual right Fourier multiplier

Source: `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CharacteristicTransport.KernelDifferentiation
open FourierIntegral
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "FV" => Fin q → ℂ

/-- The endpoint is the canonical-phase spatial PDO applied on the left of
the actual `θ β` multiplier slice. `cutPhysicalMultiplierSlice_apply` identifies
that slice with the same spacetime multiplier on `v`, so source-mask order and
physical normalization are unchanged
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem cutFixedTimeFourier_diagonal_eq_spatialPDO (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (β θ : E → ℂ) (v : SchwartzMap E FV)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (hdiag : ∀ t y η, Ψ t t y η = inner ℝ y η) (t : ℝ) (y : Euclidean d) :
    cutFixedTimeFourier Ψ b β θ v t t y =
      graphOperator (fun y η ↦ inner ℝ y η) (fun y _ η ↦ b t t y η)
        (cutPhysicalMultiplierSlice β θ v hβ hθ hθcs t) y := by
  rw [cutFixedTimeFourier_eq_graphOperator Ψ b β θ v hβ hθ hθcs]
  have he : Ψ t t = fun y η ↦ inner ℝ y η := funext fun y ↦ funext fun η ↦ hdiag t y η
  rw [he]
end JanetCartan.CharacteristicTransport.KernelDifferentiation
