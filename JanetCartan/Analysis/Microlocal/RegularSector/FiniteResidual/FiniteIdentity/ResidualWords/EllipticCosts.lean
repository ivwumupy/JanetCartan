module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords.Paired
public import JanetCartan.Analysis.Microlocal.EllipticLocalization.CommonOutputCosts

/-!
# Polynomial costs for the elliptic letter of the complete residual

Instantiate the published common-output elliptic estimates on the grouped
letter of the actual normalized residual. The original coefficient profiles
and geometric bump produce the complex and real restriction costs, including
the literal adjoint. Consumers: `finiteChain_observation_rapidDecayAt.hcost`
and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option synthInstance.maxSize 256
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.RegularSector.Realization
namespace JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
open FiniteMasks.ActualFamily EllipticComplement Characteristic.EvolutionIntegral
open Characteristic.RetardedLocalization Realization NormalizedSolver
open ArbitraryAccuracy.ResidualLocalization ArbitraryAccuracy.EvolutionLocalization
open CharacteristicTransport.CompleteResidual FourierIntegral
open FullLowBounds LowBounds LowBounds.FrequencyCutoff
open FiniteChain.Graph KernelLimits KernelEstimates
open PhysicalShells PhysicalShells.Comparable PhysicalShells.Noncomparable
open KernelEstimates.NoncomparableGeometry
open Pseudodifferential ResponseTransfer LocalSobolev
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
local notation "H" => SpacetimeL2 d (d+1)
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
local notation "χs" => fun z ↦ (f.inputMask z : ℂ)

/-- The actual grouped elliptic letter has polynomial cost in both
complex and real restriction scales, in either literal orientation. The
common-output symbol producer discharges the analytic operator bounds; full B,
the original threshold, external half and whole conjugate remain unchanged.
The fixed bump supplies the required source plateau without a Sobolev claim
for bare zero extension (`app:ch_regular:lem:finite-chain`). -/
theorem selectedFullPairedResidualTerm_elliptic_hasPolynomialRestrictionCost
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (output : E → ℝ) (houtput : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k)
    {ι : Type*} (ρ L : ι → ℝ) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i)
    (Rstar : ℕ) (hRstar : 1 ≤ Rstar) (threshold : ℝ) (ht : f.radialThreshold ≤ threshold)
    (Q : ι → E → Coeff) (B : ι → E → Mat)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) Ω) (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ω)
    (hmap : ∀ i, MapsTo (Q i) Ω (closedBall A₀ f.coefficientRadius))
    (hQl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (Q i) ≤ M)
    (hBl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (B i) ≤ M)
    (hQp : ∀ i k, cNorm (closedBall x RQ) k (Q i) ≤ AQ k * L i ^ (k-Rstar))
    (hBp : ∀ i k, cNorm (closedBall x RQ) k (B i) ≤ AB k * L i ^ (k-Rstar))
    (W₁ : ι → f.centers → TwoTimeAmplitude d (d+1))
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : ι → f.centers → H →L[ℂ] H)
    (backward : Bool) {xχ : E} (χ : ContDiffBump xχ)
    (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hs : tsupport (χ : E → ℝ) ⊆ U)
    (hp : ∀ y ∈ tsupport (if backward then (fun y ↦ (output y : ℂ)) else (χs)), χ y = 1) :
    let P := fun i ↦ selectedFullPairedResidualTerm f hK threshold (Q i) (B i) (W₁ i)
      output houtput.continuous hob hib (T i) (Sum.inr ())
    HasPolynomialSobolevCost (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU)
      (restrictionSobolevScale V (EuclideanSpace ℂ (Fin (d+1))) hV) ρ
      (fun i ↦ (localRetardedOperator hU V
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
    HasPolynomialSobolevCost (restrictionSobolevScale U (EuclideanSpace ℝ (Fin (d+1))) hU)
      (restrictionSobolevScale V (EuclideanSpace ℝ (Fin (d+1))) hV) ρ
      (fun i ↦ (localRealCompression hU V
        (if backward then (P i).adjoint else P i)).toLinearMap) := by
  intro P
  let O : H →L[ℂ] H := sourceCutMultiplier output houtput.continuous hob
  let S := fun i ↦ O.comp (ellipticResidual f hK threshold (Q i) (B i))
  have hρ i : 1 ≤ ρ i := (hL i).trans (hLρ i)
  have hρpos i : 0 < ρ i := zero_lt_one.trans_le (hρ i)
  have he i : P i = normalizedPair (S i) :=
    selectedFullPairedResidualTerm_elliptic f hK threshold (Q i) (B i) (W₁ i)
      output houtput.continuous hob hib (T i)
  have hb := EllipticLocalization.commonOutput_ellipticOperators_hasPolynomialRestrictionCost
    f hK hΩ hRQΩ output houtput hoc hos hob AQ AB hAQ hAB ρ L hL hLρ Rstar hRstar threshold ht
    Q B hQ hB hmap hQl hBl hQp hBp true backward χ U V hU hV hs hp
  have hscaled := localOperator_smul_hasPolynomialRestrictionCost ρ hρpos
    (fun i ↦ if backward then (S i).adjoint else S i) (1/2 : ℂ) U V hU hV hb
  have hc : HasPolynomialSobolevCost
      (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU)
      (restrictionSobolevScale V (EuclideanSpace ℂ (Fin (d+1))) hV) ρ
      (fun i ↦ (localRetardedOperator hU V
        (if backward then (P i).adjoint else P i)).toLinearMap) := by
    have hpaired := physicalPairedSectorSum_hasPolynomialRestrictionCost ρ hρ
      (fun _ : Unit ↦ fun i ↦ (1/2 : ℂ) • (if backward then (S i).adjoint else S i))
      {()} U V hU hV (fun _ _ ↦ hscaled)
    cases backward with
    | false => simpa only [Bool.false_eq_true, ↓reduceIte, he, normalizedPair] using hpaired
    | true => simpa only [ite_true, he, normalizedPair, physicalPairedSectorSum_adjoint_eq,
        map_smulₛₗ, map_div₀, map_one, map_ofNat] using hpaired
  exact ⟨hc, realCompression_hasPolynomialRestrictionCost ρ hρpos _ U V hU hV hc⟩

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
