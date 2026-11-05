module
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords.CharacteristicCosts

/-!
# All measured letters of one normalized complete residual

Apply the characteristic and elliptic cost producers on one supplied family.
The same endpoint and retarded certificates and full-B algebraic jets are
retained from its protected construction. Every complete conjugate pair has
complex and real polynomial restriction cost in each literal orientation;
no additional analytic cost hypothesis or family selection is introduced.
Consumer: `finiteChain_observation_rapidDecayAt.hcost`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
open Characteristic Characteristic.EvolutionIntegral Characteristic.UniformEvolution
open Characteristic.RetardedLocalization Realization NormalizedSolver FiniteAssembly
open FiniteMasks.ActualFamily FiniteAlgebraic FinitePdo FiniteEvolution
open ArbitraryAccuracy.ResidualLocalization CharacteristicTransport.CompleteResidual
open Characteristic.PdoRealization AmplitudeBound
open ResponseTransfer.Complement
open Pseudodifferential ResponseTransfer LocalSobolev FourierIntegral FourierIntegral.LowBounds
variable {d : ℕ} {ι : Type*}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "Coeff" => Fin (d+1) → Mat
local notation "H" => SpacetimeL2 d (d+1)
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- Every letter of the SAME complete residual alphabet has complex and
real measured polynomial cost in both literal orientations. The characteristic
inputs are the retained endpoint/retarded certificates and algebraic symbol
jets of the protected constructor. The elliptic inputs are derived here from
the original Q/B coefficient profiles. This supplies all factor costs to
`finiteChain_observation_rapidDecayAt`, preserving the external half, full B,
both physical masks and every reflected contribution
(`app:ch_regular:lem:finite-chain`, `energy-complete-residual`). -/
theorem selectedFullPairedResidualTerm_measured_hasPolynomialRestrictionCost_with_signed
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (threshold : ℝ) (ht : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hos : tsupport output ⊆ ball x f.physicalRadius)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
    (Rbox Ralg Malg base : f.centers → ℝ)
    (D Dgain Gain cost C : f.centers → ℕ → ℝ) (AQ AB : ℕ → ℝ)
    (hDgain : ∀ p n, 1 ≤ Dgain p n) (hGain : ∀ p n, 0 ≤ Gain p n)
    (hcost : ∀ p n, 0 ≤ cost p n) (hC : ∀ p n, 0 ≤ C p n)
    (hAQ : ∀ n, 0 ≤ AQ n) (hAB : ∀ n, 0 ≤ AB n)
    (ρ L : ι → ℝ) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i)
    (Rstar : ℕ) (hRstar : 1 ≤ Rstar)
    (Q : ι → E → Coeff) (B : ι → E → Mat)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) Ω) (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ω)
    (hmap : ∀ i, MapsTo (Q i) Ω (closedBall A₀ f.coefficientRadius))
    (hQl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (Q i) ≤ M)
    (hBl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (B i) ≤ M)
    (hQp : ∀ i k, cNorm (closedBall x RQ) k (Q i) ≤ AQ k * L i^(k-Rstar))
    (hBp : ∀ i k, cNorm (closedBall x RQ) k (B i) ≤ AB k * L i^(k-Rstar))
    (W₁ : ι → f.centers → TwoTimeAmplitude d (d+1))
    (T : ι → f.centers → H →L[ℂ] H) (Ψ : ι → f.centers → TwoTimePhase d)
    (χout χsource : f.centers → E → ℂ) (hs : ∀ p, ContDiff ℝ ∞ (χsource p))
    (hendpoint : ∀ i p, EndpointPdoEstimates (f.chart p).index (closedBall x RQ) (Q i) (B i)
      (endpointOutputMask f p output) (chartInputMask f p)
      (selectedEndpointSymbol f p threshold (Q i) (W₁ i p)) (Rbox p) M (D p) (Dgain p) (Gain p))
    (hretarded : ∀ i p, RetainedSignedRetardedBounds (closedBall x RQ) (Q i) (B i)
      (3*(f.chart p).maskRadius/4) ((coordinateSplit (f.chart p).index x).1-(f.chart p).maskRadius/2)
      (Ψ i p) (twoTimePhysicalApply
        (fun y a ↦ (ResidualCoordinates.coefficient (f.chart p).index (Q i) y a).map Complex.ofReal)
        (fun y ↦ (ResidualCoordinates.zeroth (f.chart p).index (B i) y).map Complex.ofReal) (W₁ i p))
      (χout p) (χsource p) (selectedEndpointMultiplier f p threshold) (hs p) 1
      (base p) (cost p) (T i p))
    (hnormal : ∀ i p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 1)) (Ralg p) (Malg p))
    (hjets : ∀ i p m ξ is, is.length ≤ m → ∀ z,
      (1+‖ξ‖)*‖matrixAmplitudeCoordinateDerivList is
        (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
          (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 1) ξ) z‖ ≤
        C p m*(1+cNorm (closedBall x RQ) (m+1) (Q i)+cNorm (closedBall x RQ) (m+1) (B i)))
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (U : Set E) (hU : MeasurableSet U) (hνU : tsupport ν ⊆ U)
    (hμU : tsupport μ ⊆ U) (a : (f.centers × Fin 3) ⊕ Unit) (backward : Bool) :
    let P := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (selectedFullPairedResidualTerm f hK threshold (Q i) (B i) (W₁ i)
        output ho.continuous hob hib (T i) a)
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ (fun i ↦ (localRetardedOperator hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
    HasPolynomialSobolevCost (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale U RF hU) ρ (fun i ↦ (localRealCompression hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
      ∀ reflected : Bool,
        let Ps := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
          (selectedFullPhysicalResidualTerm f hK threshold (Q i) (B i) (W₁ i)
            output ho.continuous hob hib (T i) (a, reflected))
        HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
          (restrictionSobolevScale U F hU) ρ
          (fun i ↦ (localRetardedOperator hU U
            (if backward then (Ps i).adjoint else Ps i)).toLinearMap) := by
  cases a with
  | inl a =>
    rcases a with ⟨p,j⟩
    fin_cases j
    · exact selectedFullPairedResidualTerm_endpoint_measured_hasPolynomialRestrictionCost_with_signed
        f hK p threshold output ho.continuous hob hib (Rbox p) (D p) (Dgain p) (Gain p)
        AQ AB (hDgain p) (hGain p) hAQ hAB ρ L hL hLρ Rstar Q B hQp hBp W₁ T
        (fun i ↦ hendpoint i p) μ ν hμ hν hμc hνc hμb hνb U hU hνU hμU backward
    · exact selectedFullPairedResidualTerm_retarded_measured_hasPolynomialRestrictionCost_with_signed
        f hK p threshold output ho hoc hob hib (base p) (cost p) AQ AB (hcost p)
        hAQ hAB ρ L hL hLρ Rstar Q B hQp hBp W₁ T (fun i ↦ Ψ i p)
        (χout p) (χsource p) (hs p) (fun i ↦ hretarded i p)
        μ ν hμ hν hμc hνc hμb hνb U hU hνU hμU backward
    · exact selectedFullPairedResidualTerm_algebraic_measured_hasPolynomialRestrictionCost_with_signed
        f hK p threshold output ho hoc hob hos hib (Ralg p) (Malg p) (C p) AQ AB
        (hC p) hAQ hAB ρ L hL hLρ Rstar Q B hQp hBp W₁ T (fun i ↦ hnormal i p)
        (fun i ↦ hjets i p) μ ν hμ hν hμc hνc hμb hνb U hU hνU hμU backward
  | inr a =>
    cases a
    exact selectedFullPairedResidualTerm_elliptic_measured_hasPolynomialRestrictionCost_with_signed
      f hK hΩ hRQΩ output ho hoc hob AQ AB hAQ hAB ρ L hL hLρ Rstar hRstar threshold ht
      Q B hQ hB hmap hQl hBl hQp hBp W₁ hib T μ ν hμ hν hμc hνc hμb hνb U hU hνU hμU backward

/-- Preserve the original paired complex/real restriction estimates by
projection from the same signed family (`app:ch_regular:lem:finite-chain`). -/
theorem selectedFullPairedResidualTerm_measured_hasPolynomialRestrictionCost
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (threshold : ℝ) (ht : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hos : tsupport output ⊆ ball x f.physicalRadius)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
    (Rbox Ralg Malg base : f.centers → ℝ)
    (D Dgain Gain cost C : f.centers → ℕ → ℝ) (AQ AB : ℕ → ℝ)
    (hDgain : ∀ p n, 1 ≤ Dgain p n) (hGain : ∀ p n, 0 ≤ Gain p n)
    (hcost : ∀ p n, 0 ≤ cost p n) (hC : ∀ p n, 0 ≤ C p n)
    (hAQ : ∀ n, 0 ≤ AQ n) (hAB : ∀ n, 0 ≤ AB n)
    (ρ L : ι → ℝ) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i)
    (Rstar : ℕ) (hRstar : 1 ≤ Rstar)
    (Q : ι → E → Coeff) (B : ι → E → Mat)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) Ω) (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ω)
    (hmap : ∀ i, MapsTo (Q i) Ω (closedBall A₀ f.coefficientRadius))
    (hQl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (Q i) ≤ M)
    (hBl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (B i) ≤ M)
    (hQp : ∀ i k, cNorm (closedBall x RQ) k (Q i) ≤ AQ k * L i^(k-Rstar))
    (hBp : ∀ i k, cNorm (closedBall x RQ) k (B i) ≤ AB k * L i^(k-Rstar))
    (W₁ : ι → f.centers → TwoTimeAmplitude d (d+1))
    (T : ι → f.centers → H →L[ℂ] H) (Ψ : ι → f.centers → TwoTimePhase d)
    (χout χsource : f.centers → E → ℂ) (hs : ∀ p, ContDiff ℝ ∞ (χsource p))
    (hendpoint : ∀ i p, EndpointPdoEstimates (f.chart p).index (closedBall x RQ) (Q i) (B i)
      (endpointOutputMask f p output) (chartInputMask f p)
      (selectedEndpointSymbol f p threshold (Q i) (W₁ i p)) (Rbox p) M (D p) (Dgain p) (Gain p))
    (hretarded : ∀ i p, RetainedSignedRetardedBounds (closedBall x RQ) (Q i) (B i)
      (3*(f.chart p).maskRadius/4) ((coordinateSplit (f.chart p).index x).1-(f.chart p).maskRadius/2)
      (Ψ i p) (twoTimePhysicalApply
        (fun y a ↦ (ResidualCoordinates.coefficient (f.chart p).index (Q i) y a).map Complex.ofReal)
        (fun y ↦ (ResidualCoordinates.zeroth (f.chart p).index (B i) y).map Complex.ofReal) (W₁ i p))
      (χout p) (χsource p) (selectedEndpointMultiplier f p threshold) (hs p) 1
      (base p) (cost p) (T i p))
    (hnormal : ∀ i p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 1)) (Ralg p) (Malg p))
    (hjets : ∀ i p m ξ is, is.length ≤ m → ∀ z,
      (1+‖ξ‖)*‖matrixAmplitudeCoordinateDerivList is
        (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
          (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 1) ξ) z‖ ≤
        C p m*(1+cNorm (closedBall x RQ) (m+1) (Q i)+cNorm (closedBall x RQ) (m+1) (B i)))
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (U : Set E) (hU : MeasurableSet U) (hνU : tsupport ν ⊆ U)
    (hμU : tsupport μ ⊆ U) (a : (f.centers × Fin 3) ⊕ Unit) (backward : Bool) :
    let P := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (selectedFullPairedResidualTerm f hK threshold (Q i) (B i) (W₁ i)
        output ho.continuous hob hib (T i) a)
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ (fun i ↦ (localRetardedOperator hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
    HasPolynomialSobolevCost (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale U RF hU) ρ (fun i ↦ (localRealCompression hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) := by
  have h := selectedFullPairedResidualTerm_measured_hasPolynomialRestrictionCost_with_signed
    f hK hΩ hRQΩ threshold ht output ho hoc hob hos hib Rbox Ralg Malg base
      D Dgain Gain cost C AQ AB hDgain hGain hcost hC hAQ hAB ρ L hL hLρ Rstar hRstar
      Q B hQ hB hmap hQl hBl hQp hBp W₁ T Ψ χout χsource hs hendpoint hretarded hnormal hjets
      μ ν hμ hν hμc hνc hμb hνb U hU hνU hμU a backward
  exact ⟨h.1, h.2.1⟩

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
