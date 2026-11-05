module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryAmplitudeJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.SignedCarriers

/-!
# Place the original amplitude budgets on the full critical carrier

The source cap construction gives `ε ≤ ρ/8`. The whole enlarged integration
closure, including its moving critical point, therefore fits the original
amplitude chart of radius `ρ/2`. Its actual positive conic coordinate and
bounded frequency radius give one radial band before histories or amplitudes.
Consumer: the primitive amplitude grades for both integrated envelope endpoints
in `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral UniformEvolution
open DirectEvolution
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "W" => CarrierVariables (d + 1)
local notation "Joint" => (E × Euclidean 3) × W

/-- The SAME closed critical carrier fits the original amplitude budget and
one explicit radial band. This proves, rather than assumes, the geometric
inputs of `exists_admissible_history_retained_annular_jets`. The full source
closure is retained (`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_critical_carrier_amplitude_geometry
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε ρ aperture g Rad : ℝ}
    (hε : 0 < ε) (hερ : ε ≤ ρ / 8) (hAp : 0 < aperture)
    (hg : 0 < g) (hRad : 0 < Rad)
    {Par : Set (Euclidean 3)} (hPar : IsCompact Par) :
    let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g Rad
    let K : Set Joint := (closure (elapsedPhysicalBox z ε) ×ˢ Par) ×ˢ
      closure (retainedOpenIntegrationDomain z ε O)
    IsCompact K ∧ 0 < g / 2 ∧ g / 2 < g + 1 + (1 + ‖ℓ‖) * Rad ∧
    (∀ v ∈ K, annularCarrierCoordinates v ∈ retainedGraphDomain ℓ z (ρ / 2)) ∧
    ∀ v ∈ K, ℓ (spatialPart v.2.snd) ∈ Icc (g / 2) (g + 1 + (1 + ‖ℓ‖) * Rad) := by
  intro O K
  obtain ⟨hO, hOc⟩ := retainedOpenAnnularFrequencyCarrier_open_convex ℓ z.2.2
    (ε / 2) aperture g Rad
  have hOK : IsCompact (closure O) :=
    (isCompact_closedBall (0 : E) Rad).of_isClosed_subset isClosed_closure
      (closure_minimal (fun _ h ↦ ball_subset_closedBall h.1) isClosed_closedBall)
  have hD := retainedOpenIntegrationDomain_geometry z ε hO hOc hOK
  have hX : IsCompact (closure (elapsedPhysicalBox z ε)) := by
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      isCompact_closure_retained_physicalBox z (2 * ε)
  refine ⟨(hX.prod hPar).prod hD.2.2.1,
    half_pos hg, ?_, ?_, ?_⟩
  · have hh : 0 ≤ (1 + ‖ℓ‖) * Rad := by positivity
    linarith
  · intro v hv
    have hθ := (hD.2.2.2 _ hv.2).2
    have hcone := (retained_annular_buffer_frequency_geometry ℓ z hε hAp hg hθ).1
    change v.1.1 ∈ elapsedPhysicalBox z ((ρ / 2) / 2) ∧
      spatialPart v.2.snd ∈ angularCone ℓ z.2.2 ((ρ / 2) / 2)
    have hx : v.1.1 ∈ elapsedPhysicalBox z (2 * ε) := by
      apply UniformEvolution.closure_elapsedPhysicalBox_half_subset (by positivity : 0 < 2 * ε)
      simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hv.1.1
    exact ⟨⟨ball_subset_ball (by linarith : 2 * ε ≤ (ρ / 2) / 2) hx.1,
      ball_subset_ball (by linarith : 2 * ε ≤ (ρ / 2) / 2) hx.2⟩,
      hcone.1, ball_subset_ball (by linarith : 2 * ε ≤ (ρ / 2) / 2) hcone.2⟩
  · intro v hv
    have hθ := (hD.2.2.2 _ hv.2).2
    have hgeom := retained_annular_buffer_frequency_geometry ℓ z hε hAp hg hθ
    have hlow : g ≤ ℓ (spatialPart v.2.snd) :=
      closure_minimal (s := O) (t := {θ : E | g ≤ ℓ (spatialPart θ)})
        (fun θ h ↦ (show g < ℓ (spatialPart θ) from h.2.2).le)
        (isClosed_le continuous_const (ℓ.continuous.comp spatialPartCLM.continuous)) hθ
    have hupper : ℓ (spatialPart v.2.snd) ≤ ‖ℓ‖ * Rad :=
      (le_abs_self _).trans ((ℓ.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left ((SymbolBudgets.norm_spatialPart_le _).trans hgeom.2.2) (norm_nonneg ℓ)))
    exact ⟨by linarith, by nlinarith [norm_nonneg ℓ]⟩

end JanetCartan.ResponseTransfer.RetainedFactors
