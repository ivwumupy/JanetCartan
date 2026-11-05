module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords.EllipticMeasured
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.EndpointSums
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.CommonMasks

/-!
# Measured costs of the actual characteristic residual letters

Apply the retained endpoint and signed retarded certificates and the actual
full-B algebraic symbol jets to the three characteristic letters of the
normalized complete residual. The physical coordinate changes, common masks,
external half, literal conjugates and measurement masks remain inside each
letter. The coefficient profiles have their original truncated reserves.
These estimates supply `finiteChain_observation_rapidDecayAt.hcost`; source
localization, off-relation leakage and terminal tails remain separate inputs
of the actual same-family construction (`app:ch_regular:lem:finite-chain`).
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

/-- The original high coefficient profiles supply a polynomial cost without
changing their truncated reserve (`app:ch_regular:eq:high-amplitude`). -/
private theorem coefficient_profile_le_polynomial
    (ρ L : ℝ) (hL : 1 ≤ L) (hLρ : L ≤ ρ) (Rstar k : ℕ)
    (AQ AB : ℕ → ℝ) (hAQ : 0 ≤ AQ k) (hAB : 0 ≤ AB k)
    (Q : E → Coeff) (B : E → Mat)
    (hQ : cNorm (closedBall x RQ) k Q ≤ AQ k * L^(k-Rstar))
    (hB : cNorm (closedBall x RQ) k B ≤ AB k * L^(k-Rstar)) :
    1+cNorm (closedBall x RQ) k Q+cNorm (closedBall x RQ) k B ≤
      (1+AQ k+AB k)*ρ^k := by
  have hp : L^(k-Rstar) ≤ ρ^k :=
    (pow_le_pow_right₀ hL (Nat.sub_le _ _)).trans
      (pow_le_pow_left₀ (zero_le_one.trans hL) hLρ _)
  have hq := hQ.trans (mul_le_mul_of_nonneg_left hp hAQ)
  have hb := hB.trans (mul_le_mul_of_nonneg_left hp hAB)
  have hone : (1 : ℝ) ≤ ρ^k := one_le_pow₀ (hL.trans hLρ)
  nlinarith

/-- The selected characteristic letter is the normalized literal physical
pair of that SAME chart term (`energy-complete-residual`). -/
theorem selectedFullPairedResidualTerm_characteristic
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (threshold : ℝ)
    (Q : E → Coeff) (B : E → Mat) (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : f.centers → H →L[ℂ] H)
    (p : f.centers) (j : Fin 3) :
    selectedFullPairedResidualTerm f hK threshold Q B W₁ output ho hob hib T (Sum.inl (p,j)) =
      normalizedPair (physicalOperator (f.chart p).index
        (selectedCommonChartResidualTerm f p threshold Q B (W₁ p) output ho hob hib (T p) j)) := by
  rw [selectedFullPairedResidualTerm_eq_physicalPair]
  rfl

/-- The retained endpoint certificate supplies polynomial costs of the exact
normalized measured endpoint letter and its literal adjoint. The coefficient
profiles are the original full Q/B profiles. `hendpoint` is supplied on the
SAME W₁ by `exists_finite_selected_residual_primitive_inputs` and the protected
constructor; no bound for the paired/measured letter is assumed.
Consumer: `finiteChain_observation_rapidDecayAt.hcost`
(`app:ch_regular:lem:finite-chain`, `energy-complete-residual`). -/
theorem selectedFullPairedResidualTerm_endpoint_measured_hasPolynomialRestrictionCost_with_signed
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (p : f.centers) (threshold : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
    (Rbox : ℝ) (D Dgain Gain AQ AB : ℕ → ℝ)
    (hDgain : ∀ n, 1 ≤ Dgain n) (hGain : ∀ n, 0 ≤ Gain n)
    (hAQ : ∀ n, 0 ≤ AQ n) (hAB : ∀ n, 0 ≤ AB n)
    (ρ L : ι → ℝ) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i) (Rstar : ℕ)
    (Q : ι → E → Coeff) (B : ι → E → Mat)
    (hQp : ∀ i k, cNorm (closedBall x RQ) k (Q i) ≤ AQ k * L i^(k-Rstar))
    (hBp : ∀ i k, cNorm (closedBall x RQ) k (B i) ≤ AB k * L i^(k-Rstar))
    (W₁ : ι → f.centers → TwoTimeAmplitude d (d+1))
    (T : ι → f.centers → H →L[ℂ] H)
    (hendpoint : ∀ i, EndpointPdoEstimates (f.chart p).index (closedBall x RQ) (Q i) (B i)
      (endpointOutputMask f p output) (chartInputMask f p)
      (selectedEndpointSymbol f p threshold (Q i) (W₁ i p)) Rbox M D Dgain Gain)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (U : Set E) (hU : MeasurableSet U) (hνU : tsupport ν ⊆ U)
    (hμU : tsupport μ ⊆ U) (backward : Bool) :
    let P := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (selectedFullPairedResidualTerm f hK threshold (Q i) (B i) (W₁ i)
        output ho hob hib (T i) (Sum.inl (p,0)))
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ (fun i ↦ (localRetardedOperator hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
    HasPolynomialSobolevCost (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale U RF hU) ρ (fun i ↦ (localRealCompression hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
      ∀ reflected : Bool,
        let Ps := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
          (selectedFullPhysicalResidualTerm f hK threshold (Q i) (B i) (W₁ i)
            output ho hob hib (T i) (Sum.inl (p,0), reflected))
        HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
          (restrictionSobolevScale U F hU) ρ
          (fun i ↦ (localRetardedOperator hU U
            (if backward then (Ps i).adjoint else Ps i)).toLinearMap) := by
  intro P
  let S := fun i ↦ physicalOperator (f.chart p).index
    (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
      (selectedEndpointSymbol f p threshold (Q i) (W₁ i p)))
  have hρ i : 1 ≤ ρ i := (hL i).trans (hLρ i)
  have hcost (rev : Bool) :
      HasPolynomialSobolevCost vectorFourierSobolevScale vectorFourierSobolevScale ρ
        (fun i ↦ (if rev then (S i).adjoint else S i).toLinearMap.restrictScalars ℝ) := by
    intro n
    let k := n+(2*(d+2)+11)
    let Dn := Dgain (2*(d+2)+(n+1))
    let Gn := (d+1 : ℝ)*(d+1)*Gain n
    let Cn := 1+AQ k+AB k
    have hDn : 0 ≤ Dn := zero_le_one.trans (hDgain _)
    have hGn : 0 ≤ Gn := mul_nonneg (by positivity) (hGain n)
    have hCn : 0 ≤ Cn := add_nonneg (add_nonneg zero_le_one (hAQ k)) (hAB k)
    refine ⟨n, k, Gn*(1+Dn*Cn), by positivity, ?_⟩
    intro i u hu
    have he := ((hendpoint i).2.2.2 n).1 u hu
    let V := if rev then (S i).adjoint else S i
    have hv : MemVectorFourierSobolev ((n : ℝ)+1) (V u) ∧
        vectorFourierSobolevNorm ((n : ℝ)+1) (V u) ≤ Gn*
          (vectorFourierSobolevNorm (n : ℝ) u+
            (Dn*(1+cNorm (closedBall x RQ) k (Q i)+cNorm (closedBall x RQ) k (B i)))*‖u‖) := by
      cases rev
      · exact he.1
      · exact he.2
    have horder : (n : ℝ) ≤ (n : ℝ)+1 := by linarith
    have hmem : MemVectorFourierSobolev (n : ℝ) (V u) := fun j ↦ (hv.1 j).mono horder
    have hnorm := (vectorFourierSobolevNorm_mono hv.1 horder).trans hv.2
    have hh := coefficient_profile_le_polynomial (ρ i) (L i) (hL i) (hLρ i) Rstar k
      AQ AB (hAQ k) (hAB k) (Q i) (B i) (hQp i k) (hBp i k)
    have hn0 : ‖u‖ ≤ vectorFourierSobolevNorm (n : ℝ) u := by
      simpa only [vectorFourierSobolevNorm_zero] using vectorFourierSobolevNorm_mono hu (Nat.cast_nonneg n)
    have hp : (1 : ℝ) ≤ ρ i^k := one_le_pow₀ (hρ i)
    have hhigh : Dn*(1+cNorm (closedBall x RQ) k (Q i)+cNorm (closedBall x RQ) k (B i)) ≤
        Dn*Cn*ρ i^k := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hDn
    have hn : vectorFourierSobolevNorm (n : ℝ) (V u) ≤
        (Gn*(1+Dn*Cn))*ρ i^k*vectorFourierSobolevNorm (n : ℝ) u := by
      apply hnorm.trans
      calc
        _ ≤ Gn*((ρ i^k)*vectorFourierSobolevNorm (n : ℝ) u+
            (Dn*Cn*ρ i^k)*vectorFourierSobolevNorm (n : ℝ) u) :=
          mul_le_mul_of_nonneg_left (add_le_add
            (le_mul_of_one_le_left (norm_nonneg _) hp)
            (mul_le_mul hhigh hn0 (norm_nonneg u) (by positivity))) hGn
        _ = _ := by ring
    refine ⟨hmem, ?_⟩
    change vectorFourierSobolevScale.gradeNorm n (V u) ≤ _
    simpa only [vectorFourierSobolevScale_gradeNorm n hmem,
      vectorFourierSobolevScale_gradeNorm n hu, Real.rpow_natCast] using hn
  have he i : selectedFullPairedResidualTerm f hK threshold (Q i) (B i) (W₁ i)
      output ho hob hib (T i) (Sum.inl (p,0)) = normalizedPair (S i) := by
    rw [selectedFullPairedResidualTerm_characteristic]
    rfl
  have hsigned i reflected : selectedFullPhysicalResidualTerm f hK threshold (Q i) (B i) (W₁ i)
      output ho hob hib (T i) (Sum.inl (p,0), reflected) =
        (if reflected then boundedConjugate ((1/2 : ℂ) • S i) else (1/2 : ℂ) • S i) := rfl
  simpa only [P, he, hsigned] using measured_normalizedPair_and_signed_hasPolynomialRestrictionCost ρ hρ S hcost
    μ ν hμ hν hμc hνc hμb hνb U hU hνU hμU backward

/-- The original paired estimate is retained as a projection of the same
signed-family estimate (`app:ch_regular:lem:finite-chain`). -/
theorem selectedFullPairedResidualTerm_endpoint_measured_hasPolynomialRestrictionCost
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (p : f.centers) (threshold : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
    (Rbox : ℝ) (D Dgain Gain AQ AB : ℕ → ℝ)
    (hDgain : ∀ n, 1 ≤ Dgain n) (hGain : ∀ n, 0 ≤ Gain n)
    (hAQ : ∀ n, 0 ≤ AQ n) (hAB : ∀ n, 0 ≤ AB n)
    (ρ L : ι → ℝ) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i) (Rstar : ℕ)
    (Q : ι → E → Coeff) (B : ι → E → Mat)
    (hQp : ∀ i k, cNorm (closedBall x RQ) k (Q i) ≤ AQ k * L i^(k-Rstar))
    (hBp : ∀ i k, cNorm (closedBall x RQ) k (B i) ≤ AB k * L i^(k-Rstar))
    (W₁ : ι → f.centers → TwoTimeAmplitude d (d+1))
    (T : ι → f.centers → H →L[ℂ] H)
    (hendpoint : ∀ i, EndpointPdoEstimates (f.chart p).index (closedBall x RQ) (Q i) (B i)
      (endpointOutputMask f p output) (chartInputMask f p)
      (selectedEndpointSymbol f p threshold (Q i) (W₁ i p)) Rbox M D Dgain Gain)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (U : Set E) (hU : MeasurableSet U) (hνU : tsupport ν ⊆ U)
    (hμU : tsupport μ ⊆ U) (backward : Bool) :
    let P := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (selectedFullPairedResidualTerm f hK threshold (Q i) (B i) (W₁ i)
        output ho hob hib (T i) (Sum.inl (p,0)))
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ (fun i ↦ (localRetardedOperator hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
    HasPolynomialSobolevCost (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale U RF hU) ρ (fun i ↦ (localRealCompression hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) := by
  have h := selectedFullPairedResidualTerm_endpoint_measured_hasPolynomialRestrictionCost_with_signed
    f hK p threshold output ho hob hib Rbox D Dgain Gain AQ AB hDgain hGain hAQ hAB
      ρ L hL hLρ Rstar Q B hQp hBp W₁ T hendpoint μ ν hμ hν hμc hνc hμb hνb U hU hνU hμU backward
  exact ⟨h.1, h.2.1⟩


/-- The actual PW₁ retarded letter has polynomial restriction costs with
both common masks, the external half, both measurement masks and its literal
adjoint. The retained signed certificate comes from the SAME protected
constructor as the endpoint certificate. The original Q/B reserves in that
certificate are retained; the polynomial bound only absorbs them into a
fixed frequency exponent (`energy-complete-residual`, `chain-tail`). -/
theorem selectedFullPairedResidualTerm_retarded_measured_hasPolynomialRestrictionCost_with_signed
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (p : f.centers) (threshold : ℝ)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
    (base : ℝ) (cost AQ AB : ℕ → ℝ) (hcost : ∀ n, 0 ≤ cost n)
    (hAQ : ∀ n, 0 ≤ AQ n) (hAB : ∀ n, 0 ≤ AB n)
    (ρ L : ι → ℝ) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i) (Rstar : ℕ)
    (Q : ι → E → Coeff) (B : ι → E → Mat)
    (hQp : ∀ i k, cNorm (closedBall x RQ) k (Q i) ≤ AQ k * L i^(k-Rstar))
    (hBp : ∀ i k, cNorm (closedBall x RQ) k (B i) ≤ AB k * L i^(k-Rstar))
    (W₁ : ι → f.centers → TwoTimeAmplitude d (d+1))
    (T : ι → f.centers → H →L[ℂ] H) (Ψ : ι → TwoTimePhase d)
    (χout χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (hretarded : ∀ i, RetainedSignedRetardedBounds (closedBall x RQ) (Q i) (B i)
      (3*(f.chart p).maskRadius/4) ((coordinateSplit (f.chart p).index x).1-(f.chart p).maskRadius/2)
      (Ψ i) (twoTimePhysicalApply
        (fun y a ↦ (ResidualCoordinates.coefficient (f.chart p).index (Q i) y a).map Complex.ofReal)
        (fun y ↦ (ResidualCoordinates.zeroth (f.chart p).index (B i) y).map Complex.ofReal) (W₁ i p))
      χout χsource (selectedEndpointMultiplier f p threshold) hs 1 base cost (T i p))
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (U : Set E) (hU : MeasurableSet U) (hνU : tsupport ν ⊆ U)
    (hμU : tsupport μ ⊆ U) (backward : Bool) :
    let P := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (selectedFullPairedResidualTerm f hK threshold (Q i) (B i) (W₁ i)
        output ho.continuous hob hib (T i) (Sum.inl (p,1)))
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ (fun i ↦ (localRetardedOperator hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
    HasPolynomialSobolevCost (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale U RF hU) ρ (fun i ↦ (localRealCompression hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
      ∀ reflected : Bool,
        let Ps := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
          (selectedFullPhysicalResidualTerm f hK threshold (Q i) (B i) (W₁ i)
            output ho.continuous hob hib (T i) (Sum.inl (p,1), reflected))
        HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
          (restrictionSobolevScale U F hU) ρ
          (fun i ↦ (localRetardedOperator hU U
            (if backward then (Ps i).adjoint else Ps i)).toLinearMap) := by
  intro P
  let S := fun i ↦ physicalOperator (f.chart p).index
    (selectedCommonChartRetarded f p output ho.continuous hob hib (T i p))
  have hρ i : 1 ≤ ρ i := (hL i).trans (hLρ i)
  obtain ⟨D, hD, hmasks⟩ := exists_commonMask_sobolev_constants (q := d+1)
    output f.inputMask ho f.inputMask_smooth hoc f.inputMask_compact hob hib
  have hfourier (rev : Bool) :
      HasPolynomialSobolevCost vectorFourierSobolevScale vectorFourierSobolevScale ρ
        (fun i ↦ (if rev then (S i).adjoint else S i).toLinearMap.restrictScalars ℝ) := by
    intro n
    let k := n+(FullLowBounds.fullLowReserve (d+1)+2)+10
    let An := D n*cost n*D n
    let Cn := 1+AQ k+AB k
    have hAn : 0 ≤ An := mul_nonneg
      (mul_nonneg (zero_le_one.trans (hD n)) (hcost n)) (zero_le_one.trans (hD n))
    have hCn : 0 ≤ Cn := add_nonneg (add_nonneg zero_le_one (hAQ k)) (hAB k)
    refine ⟨n, k, An*(1+Cn), by positivity, ?_⟩
    intro i u hu
    let high := retardedCoefficientProfile (closedBall x RQ) (Q i) (B i)
      (n+(FullLowBounds.fullLowReserve (d+1)+2))
    have hhpos : 0 ≤ high := by
      dsimp [high, retardedCoefficientProfile]
      linarith [cNorm_nonneg (closedBall x RQ) k (Q i),
        cNorm_nonneg (closedBall x RQ) (n+(FullLowBounds.fullLowReserve (d+1)+2)+9) (B i)]
    have hraw (V : H →L[ℂ] H)
        (hV : V = physicalOperator (f.chart p).index (T i p) ∨
          V = (physicalOperator (f.chart p).index (T i p)).adjoint)
        (v : H) (hv : MemVectorFourierSobolev (n : ℝ) v) :
        MemVectorFourierSobolev (n : ℝ) (V v) ∧
          vectorFourierSobolevNorm (n : ℝ) (V v) ≤ cost n*
            (vectorFourierSobolevNorm (n : ℝ) v+high*‖v‖) := by
      have hnle : ((n-1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
      have hv' : MemVectorFourierSobolev ((n-1 : ℕ) : ℝ) v := fun j ↦ (hv j).mono hnle
      have hb := (physicalOperator_retained_signed_bounds (f.chart p).index
        (closedBall x RQ) (Q i) (B i) _ _ (Ψ i) _ χout χsource
        (selectedEndpointMultiplier f p threshold) hs 1 base cost (T i p) (hretarded i)).1
        n V hV v hv'
      exact ⟨hb.1, hb.2.trans (mul_le_mul_of_nonneg_left
        (add_le_add (vectorFourierSobolevNorm_mono hv hnle) le_rfl) (hcost n))⟩
    let V := if rev then (S i).adjoint else S i
    have hb := hmasks (physicalOperator (f.chart p).index (T i p)) n n
      (cost n) high (hcost n) hhpos hraw V (by
        dsimp only [V, S]
        rw [physicalOperator_selectedCommonChartRetarded]
        cases rev <;> simp) u hu
    have hp := coefficient_profile_le_polynomial (ρ i) (L i) (hL i) (hLρ i) Rstar k
      AQ AB (hAQ k) (hAB k) (Q i) (B i) (hQp i k) (hBp i k)
    have hh : high ≤ Cn*ρ i^k := by
      apply le_trans ?_ hp
      dsimp only [high, retardedCoefficientProfile]
      exact add_le_add le_rfl (cNorm_mono_order (by dsimp [k]; omega))
    have hn0 : ‖u‖ ≤ vectorFourierSobolevNorm (n : ℝ) u := by
      simpa only [vectorFourierSobolevNorm_zero] using vectorFourierSobolevNorm_mono hu (Nat.cast_nonneg n)
    have hone : (1 : ℝ) ≤ ρ i^k := one_le_pow₀ (hρ i)
    have hn : vectorFourierSobolevNorm (n : ℝ) (V u) ≤
        (An*(1+Cn))*ρ i^k*vectorFourierSobolevNorm (n : ℝ) u := by
      apply hb.2.trans
      calc
        _ ≤ An*((ρ i^k)*vectorFourierSobolevNorm (n : ℝ) u+
            (Cn*ρ i^k)*vectorFourierSobolevNorm (n : ℝ) u) :=
          mul_le_mul_of_nonneg_left (add_le_add
            (le_mul_of_one_le_left (norm_nonneg _) hone)
            (mul_le_mul hh hn0 (norm_nonneg u) (by positivity))) hAn
        _ = _ := by ring
    refine ⟨hb.1, ?_⟩
    change vectorFourierSobolevScale.gradeNorm n (V u) ≤ _
    simpa only [vectorFourierSobolevScale_gradeNorm n hb.1,
      vectorFourierSobolevScale_gradeNorm n hu, Real.rpow_natCast] using hn
  have he i : selectedFullPairedResidualTerm f hK threshold (Q i) (B i) (W₁ i)
      output ho.continuous hob hib (T i) (Sum.inl (p,1)) = normalizedPair (S i) := by
    rw [selectedFullPairedResidualTerm_characteristic]
    rfl
  have hsigned i reflected : selectedFullPhysicalResidualTerm f hK threshold (Q i) (B i) (W₁ i)
      output ho.continuous hob hib (T i) (Sum.inl (p,1), reflected) =
        (if reflected then boundedConjugate ((1/2 : ℂ) • S i) else (1/2 : ℂ) • S i) := rfl
  simpa only [P, he, hsigned] using measured_normalizedPair_and_signed_hasPolynomialRestrictionCost ρ hρ S hfourier
    μ ν hμ hν hμc hνc hμb hνb U hU hνU hμU backward

/-- The original paired estimate is retained as a projection of the same
signed-family estimate (`app:ch_regular:lem:finite-chain`). -/
theorem selectedFullPairedResidualTerm_retarded_measured_hasPolynomialRestrictionCost
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (p : f.centers) (threshold : ℝ)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
    (base : ℝ) (cost AQ AB : ℕ → ℝ) (hcost : ∀ n, 0 ≤ cost n)
    (hAQ : ∀ n, 0 ≤ AQ n) (hAB : ∀ n, 0 ≤ AB n)
    (ρ L : ι → ℝ) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i) (Rstar : ℕ)
    (Q : ι → E → Coeff) (B : ι → E → Mat)
    (hQp : ∀ i k, cNorm (closedBall x RQ) k (Q i) ≤ AQ k * L i^(k-Rstar))
    (hBp : ∀ i k, cNorm (closedBall x RQ) k (B i) ≤ AB k * L i^(k-Rstar))
    (W₁ : ι → f.centers → TwoTimeAmplitude d (d+1))
    (T : ι → f.centers → H →L[ℂ] H) (Ψ : ι → TwoTimePhase d)
    (χout χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (hretarded : ∀ i, RetainedSignedRetardedBounds (closedBall x RQ) (Q i) (B i)
      (3*(f.chart p).maskRadius/4) ((coordinateSplit (f.chart p).index x).1-(f.chart p).maskRadius/2)
      (Ψ i) (twoTimePhysicalApply
        (fun y a ↦ (ResidualCoordinates.coefficient (f.chart p).index (Q i) y a).map Complex.ofReal)
        (fun y ↦ (ResidualCoordinates.zeroth (f.chart p).index (B i) y).map Complex.ofReal) (W₁ i p))
      χout χsource (selectedEndpointMultiplier f p threshold) hs 1 base cost (T i p))
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (U : Set E) (hU : MeasurableSet U) (hνU : tsupport ν ⊆ U)
    (hμU : tsupport μ ⊆ U) (backward : Bool) :
    let P := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (selectedFullPairedResidualTerm f hK threshold (Q i) (B i) (W₁ i)
        output ho.continuous hob hib (T i) (Sum.inl (p,1)))
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ (fun i ↦ (localRetardedOperator hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
    HasPolynomialSobolevCost (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale U RF hU) ρ (fun i ↦ (localRealCompression hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) := by
  have h := selectedFullPairedResidualTerm_retarded_measured_hasPolynomialRestrictionCost_with_signed
    f hK p threshold output ho hoc hob hib base cost AQ AB hcost hAQ hAB
      ρ L hL hLρ Rstar Q B hQp hBp W₁ T Ψ χout χsource hs hretarded
      μ ν hμ hν hμc hνc hμb hνb U hU hνU hμU backward
  exact ⟨h.1, h.2.1⟩


/-- The algebraic derivative letter, with full B and the original doubled
radial collar, has polynomial costs after physical transport, the common
output, the external half and measurement. The normal and coordinate-jet
certificates are exactly the corresponding conclusions of
`exists_finite_physical_algebraic_pdos_of_selected_collar`. The PDO estimate
is proved from those jets; no operator bound is added as a premise
(`energy-complete-residual`, `app:ch_regular:lem:finite-chain`). -/
theorem selectedFullPairedResidualTerm_algebraic_measured_hasPolynomialRestrictionCost_with_signed
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (p : f.centers) (threshold : ℝ)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hos : tsupport output ⊆ ball x f.physicalRadius)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
    (Rbox Mbound : ℝ) (C AQ AB : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n)
    (hAQ : ∀ n, 0 ≤ AQ n) (hAB : ∀ n, 0 ≤ AB n)
    (ρ L : ι → ℝ) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i) (Rstar : ℕ)
    (Q : ι → E → Coeff) (B : ι → E → Mat)
    (hQp : ∀ i k, cNorm (closedBall x RQ) k (Q i) ≤ AQ k * L i^(k-Rstar))
    (hBp : ∀ i k, cNorm (closedBall x RQ) k (B i) ≤ AB k * L i^(k-Rstar))
    (W₁ : ι → f.centers → TwoTimeAmplitude d (d+1))
    (T : ι → f.centers → H →L[ℂ] H)
    (hnormal : ∀ i, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 1)) Rbox Mbound)
    (hjets : ∀ i m ξ is, is.length ≤ m → ∀ z,
      (1+‖ξ‖)*‖matrixAmplitudeCoordinateDerivList is
        (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
          (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 1) ξ) z‖ ≤
        C m*(1+cNorm (closedBall x RQ) (m+1) (Q i)+cNorm (closedBall x RQ) (m+1) (B i)))
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (U : Set E) (hU : MeasurableSet U) (hνU : tsupport ν ⊆ U)
    (hμU : tsupport μ ⊆ U) (backward : Bool) :
    let P := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (selectedFullPairedResidualTerm f hK threshold (Q i) (B i) (W₁ i)
        output ho.continuous hob hib (T i) (Sum.inl (p,2)))
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ (fun i ↦ (localRetardedOperator hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
    HasPolynomialSobolevCost (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale U RF hU) ρ (fun i ↦ (localRealCompression hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
      ∀ reflected : Bool,
        let Ps := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
          (selectedFullPhysicalResidualTerm f hK threshold (Q i) (B i) (W₁ i)
            output ho.continuous hob hib (T i) (Sum.inl (p,2), reflected))
        HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
          (restrictionSobolevScale U F hU) ρ
          (fun i ↦ (localRetardedOperator hU U
            (if backward then (Ps i).adjoint else Ps i)).toLinearMap) := by
  intro P
  let A := fun i ↦ maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p)
    (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 1)
  let S := fun i ↦ (1/Complex.I) • ((sourceCutMultiplier output ho.continuous hob).comp
    (physicalOperator (f.chart p).index (A i)))
  have hρ i : 1 ≤ ρ i := (hL i).trans (hLρ i)
  obtain ⟨Dmask, hDmask, hmasks⟩ := exists_outputMask_sobolev_constants (q := d+1)
    output ho hoc hob
  have hfourier (rev : Bool) :
      HasPolynomialSobolevCost vectorFourierSobolevScale vectorFourierSobolevScale ρ
        (fun i ↦ (if rev then (S i).adjoint else S i).toLinearMap.restrictScalars ℝ) := by
    intro n
    let m := 2*(d+2)+n
    let b := 2*(d+2)+1
    let Cn := C m*(1+AQ (m+1)+AB (m+1))
    have hCn : 0 ≤ Cn := mul_nonneg (hC m)
      (add_nonneg (add_nonneg zero_le_one (hAQ _)) (hAB _))
    obtain ⟨D, hD, hbound⟩ := exists_maskedPhysicalPDO_polynomial_fourier_constant
      (d := d) (q := d+1) Rbox Mbound n b Cn hCn
    refine ⟨n, (n+b : ℕ), Dmask n*D*Dmask n, mul_nonneg
      (mul_nonneg (zero_le_one.trans (hDmask n)) hD) (zero_le_one.trans (hDmask n)), ?_⟩
    intro i u hu
    have hhigh ξ is (his : is.length ≤ 2*(d+1+1)+n) z :
        ‖matrixAmplitudeCoordinateDerivList is
          (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 1) ξ) z‖ ≤
          Cn * L i^(n+b) := by
      have hj := hjets i m ξ is (by simpa only [m, Nat.add_assoc] using his) z
      have hw := le_mul_of_one_le_left (norm_nonneg
        (matrixAmplitudeCoordinateDerivList is
          (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 1) ξ) z))
        (by linarith [norm_nonneg ξ] : (1 : ℝ) ≤ 1+‖ξ‖)
      have hp := coefficient_profile_le_polynomial (L i) (L i) (hL i) le_rfl Rstar (m+1)
        AQ AB (hAQ _) (hAB _) (Q i) (B i) (hQp i _) (hBp i _)
      have hmb : m+1 = n+b := by dsimp [m, b]; omega
      calc
        _ ≤ C m*(1+cNorm (closedBall x RQ) (m+1) (Q i)+
            cNorm (closedBall x RQ) (m+1) (B i)) := hw.trans hj
        _ ≤ C m*((1+AQ (m+1)+AB (m+1))*L i^(m+1)) :=
          mul_le_mul_of_nonneg_left hp (hC m)
        _ = _ := by dsimp only [Cn]; rw [hmb]; ring
    have hraw V (hV : V = physicalOperator (f.chart p).index (A i) ∨
        V = (physicalOperator (f.chart p).index (A i)).adjoint) v
        (hv : MemVectorFourierSobolev (n : ℝ) v) :
        MemVectorFourierSobolev (n : ℝ) (V v) ∧
          vectorFourierSobolevNorm (n : ℝ) (V v) ≤
            (D*ρ i^(n+b))*(vectorFourierSobolevNorm (n : ℝ) v+0*‖v‖) := by
      have hc W (hW : W = A i ∨ W = (A i).adjoint) z
          (hz : MemVectorFourierSobolev (n : ℝ) z) :=
        hbound (ρ i) (L i) (hL i) (hLρ i) (chartOutputMask f p) (chartInputMask f p)
          (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 1)
          (hnormal i) hhigh W hW z hz
      rcases hV with rfl | rfl
      · apply physicalOperator_sobolev_bound (f.chart p).index (A i)
          (n : ℝ) (n : ℝ) (D*ρ i^(n+b)) 0 _ v hv
        intro z hz
        simpa only [zero_mul, add_zero] using hc (A i) (Or.inl rfl) z hz
      · rw [physicalOperator_adjoint]
        apply physicalOperator_sobolev_bound (f.chart p).index (A i).adjoint
          (n : ℝ) (n : ℝ) (D*ρ i^(n+b)) 0 _ v hv
        intro z hz
        simpa only [zero_mul, add_zero] using hc (A i).adjoint (Or.inr rfl) z hz
    have hm := hmasks (physicalOperator (f.chart p).index (A i)) n n
      (D*ρ i^(n+b)) 0 (mul_nonneg hD (pow_nonneg (zero_le_one.trans (hρ i)) _)) le_rfl hraw
    let V := if rev then (S i).adjoint else S i
    have hb := direct_sobolev_unit_smul _ (1/Complex.I) (by simp) (n : ℝ) (n : ℝ)
      (Dmask n*(D*ρ i^(n+b))*Dmask n) 0 hm V (by cases rev <;> simp [V, S]) u hu
    refine ⟨hb.1, ?_⟩
    change vectorFourierSobolevScale.gradeNorm n (V u) ≤ _
    simpa only [vectorFourierSobolevScale_gradeNorm n hb.1,
      vectorFourierSobolevScale_gradeNorm n hu, Real.rpow_natCast, zero_mul, add_zero,
      mul_assoc, mul_comm, mul_left_comm] using hb.2
  have hbase i : FiniteEvolution.physicalOperator (f.chart p).index
      (selectedCommonChartResidualTerm f p threshold (Q i) (B i) (W₁ i p)
        output ho.continuous hob hib (T i p) 2) = S i := by
    change FiniteEvolution.physicalOperator (f.chart p).index ((1/Complex.I) •
      maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 1)) = S i
    have hm := commonOutput_comp_chartPDO f p output ho.continuous hob hos
      (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 1) Rbox Mbound (hnormal i)
    dsimp only [S]
    rw [show (sourceCutMultiplier output ho.continuous hob).comp
      (physicalOperator (f.chart p).index (A i)) = _ from hm]
    simp only [FiniteEvolution.physicalOperator, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  have he i : selectedFullPairedResidualTerm f hK threshold (Q i) (B i) (W₁ i)
      output ho.continuous hob hib (T i) (Sum.inl (p,2)) = normalizedPair (S i) := by
    rw [selectedFullPairedResidualTerm_characteristic, hbase]
  have hsigned i reflected : selectedFullPhysicalResidualTerm f hK threshold (Q i) (B i) (W₁ i)
      output ho.continuous hob hib (T i) (Sum.inl (p,2), reflected) =
        (if reflected then boundedConjugate ((1/2 : ℂ) • S i) else (1/2 : ℂ) • S i) := by
    simp only [selectedFullPhysicalResidualTerm, Sum.elim_inl, hbase]
  simpa only [P, he, hsigned] using measured_normalizedPair_and_signed_hasPolynomialRestrictionCost
    ρ hρ S hfourier μ ν hμ hν hμc hνc hμb hνb U hU hνU hμU backward

/-- The original paired estimate is retained as a projection of the same
signed-family estimate (`app:ch_regular:lem:finite-chain`). -/
theorem selectedFullPairedResidualTerm_algebraic_measured_hasPolynomialRestrictionCost
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (p : f.centers) (threshold : ℝ)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hos : tsupport output ⊆ ball x f.physicalRadius)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
    (Rbox Mbound : ℝ) (C AQ AB : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n)
    (hAQ : ∀ n, 0 ≤ AQ n) (hAB : ∀ n, 0 ≤ AB n)
    (ρ L : ι → ℝ) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i) (Rstar : ℕ)
    (Q : ι → E → Coeff) (B : ι → E → Mat)
    (hQp : ∀ i k, cNorm (closedBall x RQ) k (Q i) ≤ AQ k * L i^(k-Rstar))
    (hBp : ∀ i k, cNorm (closedBall x RQ) k (B i) ≤ AB k * L i^(k-Rstar))
    (W₁ : ι → f.centers → TwoTimeAmplitude d (d+1))
    (T : ι → f.centers → H →L[ℂ] H)
    (hnormal : ∀ i, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 1)) Rbox Mbound)
    (hjets : ∀ i m ξ is, is.length ≤ m → ∀ z,
      (1+‖ξ‖)*‖matrixAmplitudeCoordinateDerivList is
        (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
          (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 1) ξ) z‖ ≤
        C m*(1+cNorm (closedBall x RQ) (m+1) (Q i)+cNorm (closedBall x RQ) (m+1) (B i)))
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (U : Set E) (hU : MeasurableSet U) (hνU : tsupport ν ⊆ U)
    (hμU : tsupport μ ⊆ U) (backward : Bool) :
    let P := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (selectedFullPairedResidualTerm f hK threshold (Q i) (B i) (W₁ i)
        output ho.continuous hob hib (T i) (Sum.inl (p,2)))
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ (fun i ↦ (localRetardedOperator hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
    HasPolynomialSobolevCost (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale U RF hU) ρ (fun i ↦ (localRealCompression hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) := by
  have h := selectedFullPairedResidualTerm_algebraic_measured_hasPolynomialRestrictionCost_with_signed
    f hK p threshold output ho hoc hob hos hib Rbox Mbound C AQ AB hC hAQ hAB
      ρ L hL hLρ Rstar Q B hQp hBp W₁ T hnormal hjets μ ν hμ hν hμc hνc hμb hνb U hU hνU hμU backward
  exact ⟨h.1, h.2.1⟩

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
