module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedEndpointSymbol.Endpoint
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedEndpointSymbol.RetainedProfiles

/-!
# The original derivative reserve in the supplied normalized endpoint

The normalized band initializer retains the SAME `W₁` with its actual
order-minus-one seminorm certificate. The original coefficient profiles,
that certificate, the selected diagonal coverage and the fixed physical
masks produce reserved jets of the literal `Q₀W₁` endpoint symbol. No bound
on the resulting symbol is assumed, and no operator or amplitude is selected.

The consumer is the endpoint letter in the finite residual words of
`app:ch_response:eq:fixed-factor-transfer`. Its near-carrier estimate uses
`DiagonalPdo.exists_diagonalPDO_joint_sobolev_of_primitive_jets` after the
finite-scale arithmetic in `ReserveCompression`. Sources also include
`app:ch_regular:eq:high-amplitude` and
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization

open RegularSector RegularSector.FinitePdo RegularSector.FinitePdo.RetainedConstruction
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic
open RegularSector.Characteristic RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.ConicPhase RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteChain.Graph FiniteChain.Graph.PhysicalShells
open FiniteChain.Graph.PhysicalShells.Noncomparable
open ResidualLocalization

variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => JointVariables E

/-- The actual retained amplitude certificate and original coefficient
profiles produce the full reserved endpoint symbol, on any fixed normalized
annular carrier. All constants precede the reserve, scales, coefficients and
supplied `W₁`; both Hilbert orientations retain the same masks and the exact
order-minus-one weights. The output `L^(m-Rreserve)` is stronger than the
`L^(m+2-Rreserve)` primitive required by the diagonal PDO theorem
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_selected_endpoint_symbol_reserved_grades
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (threshold : ℝ) (ht : 1 ≤ threshold) (hft : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (hbuffer : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hmask : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    (ra rb : f.centers → ℝ)
    (hcoverage : ∀ p, DiagonalFrequencyCoverage (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2 ((f.chart p).bufferRadius/2)
      (ra p) (rb p) (selectedEndpointMultiplier f p threshold))
    (Jpdo : f.centers → Set V) (hJpdo : ∀ p, IsCompact (Jpdo p))
    (hpos : ∀ p, ∀ v ∈ Jpdo p, v.1.1 ∈ tsupport (endpointOutputMask f p output))
    {a : ℝ} (ha : 0 < a) (hfreq : ∀ p, ∀ v ∈ Jpdo p, a ≤ ‖v.2.1‖)
    (AQ AB : ℕ → ℝ) (cost : f.centers → ℕ → ℝ)
    (hAQ : ∀ m, 0 ≤ AQ m) (hAB : ∀ m, 0 ≤ AB m)
    (hcost : ∀ p m, 0 ≤ cost p m) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ (Rreserve Rcoeff : ℕ), Rreserve+10 ≤ Rcoeff →
      ∀ (L ρ : ℝ), 1 ≤ L → 1 ≤ ρ →
      ∀ Q : E → Fin (d+1) → MetricTensor (d+1), ContDiffOn ℝ ∞ Q Ω →
      ∀ B : E → MetricTensor (d+1),
      (∀ m, cNorm (closedBall x RQ) m Q ≤ AQ m * L ^ (m-Rcoeff)) →
      (∀ m, cNorm (closedBall x RQ) m B ≤ AB m * L ^ (m-Rcoeff)) →
      ∀ W : f.centers → TwoTimeAmplitude d (d+1),
      let J := fun p ↦
        let e := coordinateSplit (f.chart p).index
        let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
        bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius/2) (ra p) (rb p)
      (∀ p, ContDiff ℝ ∞ (jointAmplitude (W p))) →
      (∀ p m, BoundedTwoTimeOrderSeminorm 1 (J p) m (W p) ∧
        twoTimeOrderSeminorm 1 (J p) m (W p) ≤ cost p m *
          (1+cNorm (closedBall x RQ) (m+10) Q+cNorm (closedBall x RQ) (m+9) B)) →
      ∀ p backward,
      let A := orientedMaskedPDOAmplitude backward
        (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointSymbol f p threshold Q (W p))
      (∀ v ∈ Jpdo p, ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : V ↦ A w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
          ρ⁻¹ * D m * L ^ (m-Rreserve)) ∧
      (∀ low l, ∀ ξ ∈ normalizedGraphCarrier ρ low l,
        ∀ z ∈ tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p), ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : E × E ↦ A w.1 w.2 (ρ • ξ)) z‖ ≤
          (max 1 (branchRadius low l))⁻¹ * D m * L ^ (m-Rreserve)) := by
  obtain ⟨DW, hDW, hamp⟩ := exists_selected_endpoint_reserved_amplitude_profile
    f ra rb cost hcost AQ AB hAQ hAB
  obtain ⟨D, hD, hfull⟩ := exists_selected_endpoint_symbol_grades_of_reserved_seminorms
    f hΩ hball threshold ht hft output ho hoc hout hbuffer hmask ra rb hcoverage
    Jpdo hJpdo hpos ha hfreq AQ DW hAQ hDW
  refine ⟨D, hD, ?_⟩
  intro Rreserve Rcoeff hR L ρ hL hρ Q hQ B hQbound hBbound W J hW hbudget p backward
  have hQreserved m : cNorm (closedBall x RQ) m Q ≤ AQ m * L ^ (m-Rreserve) :=
    (hQbound m).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega : m-Rcoeff ≤ m-Rreserve)) (hAQ m))
  exact hfull Rreserve L ρ hL hρ Q hQ hQreserved W hW
    (hamp Rreserve Rcoeff hR L hL Q B hQbound hBbound W hbudget) p backward

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
