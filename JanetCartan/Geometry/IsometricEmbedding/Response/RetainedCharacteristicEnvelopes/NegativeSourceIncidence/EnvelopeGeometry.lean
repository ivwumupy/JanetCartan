module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.NegativeSourceIncidence.Phase
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.EnvelopeGeometry

/-!
# Original radial bounds for the negative source phase

Negation preserves the original source differential norms. The same actual
source bounds therefore supply the annulus chosen before the negative
stationary carrier, for `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse LeadingWave.FullModulation
open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d

/-- The entire source sign has no effect on its physical differential norm.
This transports the actual gradient bands to the negative phase
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem negativeFullSourcePhaseInCoordinates_fderiv_norm
    (i : Fin (d + 1)) (Q : _) (x : E) (c : Param) :
    ‖fderiv ℝ (fun y ↦ T.negativeFullSourcePhaseInCoordinates i Q y c) x‖ =
      ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates i Q y c) x‖ := by
  simp only [negativeFullSourcePhaseInCoordinates, fderiv_fun_neg, norm_neg]

/-- The same actual frozen Hamilton covectors bound their negatives away
from zero on the original compact parameter support
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_negative_full_source_frozen_gradient_bounds_on_compact
    {Csrc : Set Param} (hCsrc : IsCompact Csrc)
    (hcsrc : ∀ c ∈ Csrc,
      c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius) :
    ∃ normLo > (0 : ℝ), ∃ normHi > (0 : ℝ),
      ∀ c ∈ Csrc, normLo ≤ ‖-T.reference.covector (0, c.2)‖ ∧
        ‖-T.reference.covector (0, c.2)‖ ≤ normHi := by
  simpa only [norm_neg] using
    T.exists_full_source_frozen_gradient_bounds_on_compact hCsrc hcsrc

/-- Apply the actual original differential producer on the entire physical
incidence compact, then negate its phase. Constants and the coefficient
threshold precede the stationary annulus, masks and field
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_negative_full_source_gradient_band_on_physical_incidence
    (i : Fin (d + 1)) (z : RootState (Euclidean d)) (ε : ℝ)
    {A : Set Param} (hA : IsCompact A)
    (hprimary : ∀ q ∈ closure (elapsedPhysicalBox z ε) ×ˢ A,
      ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T) :
    ∃ sourceLower sourceUpper δ : ℝ,
      0 < sourceLower ∧ sourceLower < sourceUpper ∧ 0 < δ ∧ δ ≤ T.family.threshold ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ q ∈ closure (elapsedPhysicalBox z ε) ×ˢ A,
        sourceLower ≤ ‖fderiv ℝ (fun y ↦ T.negativeFullSourcePhaseInCoordinates i Q y q.2) q.1‖ ∧
        ‖fderiv ℝ (fun y ↦ T.negativeFullSourcePhaseInCoordinates i Q y q.2) q.1‖ ≤ sourceUpper := by
  simpa only [T.negativeFullSourcePhaseInCoordinates_fderiv_norm] using
    T.exists_full_source_gradient_band_on_physical_incidence i z ε hA hprimary

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
