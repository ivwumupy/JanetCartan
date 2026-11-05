module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.TailSymbols.SourceSlice
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.TailSymbols.Masks

/-!
# Actual endpoint symbol inputs for the complete PDO tail

Apply the SAME endpoint certificate retained by the selected inverse.
Its original `j+10` coefficient budgets and the original coefficient reserve
give the physical source-kernel profile. The full frequency variable and
both physical masks remain literal throughout.

Consumer: `FullEllipticResidualEnvelopes.completeDiagonalAnnularComplement_sobolev`
(`app:ch_response:eq:direct-envelope-profile`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
open TailSymbols
open RegularSector RegularSector.FiniteMasks.ActualFamily RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open RegularSector.Characteristic RegularSector.Characteristic.PdoRealization
open RegularSector.Characteristic.ResidualCoordinates RegularSector.Characteristic.EvolutionIntegral
open CharacteristicTransport.CompleteResidual FourierIntegral AmplitudeBound

variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- Global physical symbol profiles for the actual selected endpoint, with
constants fixed before histories and scales. The only symbol certificate is
the original `EndpointPdoEstimates`, produced by
`exists_selected_endpoint_constants` and retained in the supplied inverse.
No tail estimate or Fréchet symbol profile is an assumption
(`app:ch_regular_base:eq:energy-complete-residual`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_selected_endpoint_tail_symbol_profiles
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (hos : tsupport output ⊆ ball x f.physicalRadius)
    (threshold : ℝ) (D AQ AB : ℕ → ℝ)
    (hD : ∀ j, 0 ≤ D j) (hAQ : ∀ j, 0 ≤ AQ j) (hAB : ∀ j, 0 ≤ AB j) :
    ∃ Bσ : ℕ → ℝ, (∀ j, 0 ≤ Bσ j) ∧
      ∀ Rcoef : ℕ, 10 ≤ Rcoef → ∀ L : ℝ, 1 ≤ L →
      ∀ (Q : E → Coeff) (B : E → Mat) (W : TwoTimeAmplitude d (d+1)),
        (∀ j, cNorm (closedBall x RQ) j Q ≤ AQ j * L^(j-Rcoef)) →
        (∀ j, cNorm (closedBall x RQ) j B ≤ AB j * L^(j-Rcoef)) →
      ∀ (R : ℝ) (Dgain G : ℕ → ℝ),
        EndpointPdoEstimates (f.chart p).index (closedBall x RQ) Q B
          (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointSymbol f p threshold Q W) R M D Dgain G →
        let σa := fun y ξ ↦ endpointOutputMask f p output y • selectedEndpointSymbol f p threshold Q W y ξ
        ContDiff ℝ ∞ (Function.uncurry σa) ∧
        (∀ j ξ y, ‖iteratedFDeriv ℝ j (fun z ↦ σa z ξ) y‖ ≤ Bσ j * L^j) ∧
        (∃ R N, GraphNormalAmplitudeBounds
          (maskedPhysicalPDOCycleSymbol (chartInputMask f p) (chartInputMask f p) σa) R N) ∧
        maskedPhysicalPDO (chartInputMask f p) (chartInputMask f p) σa =
          maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
            (selectedEndpointSymbol f p threshold Q W) := by
  obtain ⟨C, hC, hslice⟩ := exists_cycle_source_slice_constants (d := d) (q := d+1)
  let Ebound := fun j ↦ D j * (1 + AQ (j+10) + AB (j+10))
  have hEbound j : 0 ≤ Ebound j :=
    mul_nonneg (hD j) (by linarith [hAQ (j+10), hAB (j+10)])
  refine ⟨fun j ↦ C j * Ebound j, fun j ↦ mul_nonneg (hC j) (hEbound j), ?_⟩
  intro Rcoef hR L hL Q B W hQp hBp R Dgain G hcertificate σa
  have hscale j : 1 + cNorm (closedBall x RQ) (j+10) Q + cNorm (closedBall x RQ) (j+10) B ≤
      (1 + AQ (j+10) + AB (j+10)) * L^j := by
    have hp : L^(j+10-Rcoef) ≤ L^j := pow_le_pow_right₀ hL (by omega)
    have hq := (hQp (j+10)).trans (mul_le_mul_of_nonneg_left hp (hAQ _))
    have hb := (hBp (j+10)).trans (mul_le_mul_of_nonneg_left hp (hAB _))
    have h1 : (1 : ℝ) ≤ L^j := one_le_pow₀ hL
    nlinarith
  have hcoords j ξ is (his : is.length ≤ j) z :
      ‖matrixAmplitudeCoordinateDerivList is
        (maskedPhysicalPDOCycleSymbol (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointSymbol f p threshold Q W) ξ) z‖ ≤ Ebound j * L^j := by
    apply (le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg ξ] : 1 ≤ 1+‖ξ‖)).trans
    apply (hcertificate.2.2.1 j ξ is his z).trans
    exact (mul_le_mul_of_nonneg_left (hscale j) (hD j)).trans_eq (by dsimp [Ebound]; ring)
  obtain ⟨hσa, hj⟩ := hslice (endpointOutputMask f p output) (chartInputMask f p)
    ((physicalCoordinates (f.chart p).index).symm x) (chartInputMask_eq_one_at_center f p)
    (selectedEndpointSymbol f p threshold Q W) R _ hcertificate.1
    (fun j ↦ Ebound j * L^j) (fun j ↦ mul_nonneg (hEbound j)
      (pow_nonneg (zero_le_one.trans hL) j)) hcoords
  refine ⟨hσa, ?_, ?_, maskedPhysicalPDO_chartInput_output_absorption f p output hos _⟩
  · intro j ξ y
    exact (hj j ξ y).trans_eq (by ring)
  · refine ⟨R, D (2*(d+2)+1) * (1+M+M), ?_⟩
    rw [show σa = fun y ξ ↦ endpointOutputMask f p output y •
      selectedEndpointSymbol f p threshold Q W y ξ from rfl,
      absorbed_selected_cycleSymbol_eq f p output hos]
    exact hcertificate.1

end JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
