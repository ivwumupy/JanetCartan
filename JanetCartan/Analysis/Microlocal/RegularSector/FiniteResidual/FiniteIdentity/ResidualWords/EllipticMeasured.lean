module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords.MeasuredPairCosts

/-!
# Costs of the measured elliptic letter in every complete residual word

The published elliptic coefficient estimates produce a uniform Fourier bound.
Apply the actual measurement masks to its two literal orientations, then retain
its external half and whole conjugate before real compression. This supplies
the elliptic part of `finiteChain_observation_rapidDecayAt.hcost` for the
measured word expansion, with the original full B and threshold unchanged.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option synthInstance.maxSize 256
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
open FiniteMasks.ActualFamily EllipticComplement Characteristic.EvolutionIntegral
open Characteristic.RetardedLocalization Realization NormalizedSolver FiniteAssembly
open ArbitraryAccuracy.ResidualLocalization CharacteristicTransport.CompleteResidual
open Pseudodifferential ResponseTransfer LocalSobolev FourierIntegral FourierIntegral.LowBounds
open ResponseTransfer.Complement
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "Coeff" => Fin (d+1) → Mat
local notation "H" => SpacetimeL2 d (d+1)
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- The elliptic letter of the actual complete residual retains polynomial
restriction cost with both measurement masks inside each factor. The masks'
actual supports justify localization; no positive Sobolev estimate for bare
zero extension is used. The literal adjoint exchanges these same masks, and
real compression retains the same domain (`app:ch_regular:lem:finite-chain`,
`app:ch_regular_base:eq:measured-adjoint`). -/
theorem selectedFullPairedResidualTerm_elliptic_measured_hasPolynomialRestrictionCost_with_signed
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (output : E → ℝ) (houtput : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1)
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
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (U : Set E) (hU : MeasurableSet U)
    (hνU : tsupport ν ⊆ U) (hμU : tsupport μ ⊆ U) (backward : Bool) :
    let P := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (selectedFullPairedResidualTerm f hK threshold (Q i) (B i) (W₁ i)
        output houtput.continuous hob hib (T i) (Sum.inr ()))
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ
      (fun i ↦ (localRetardedOperator hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
    HasPolynomialSobolevCost (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale U RF hU) ρ
      (fun i ↦ (localRealCompression hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
      ∀ reflected : Bool,
        let Ps := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
          (selectedFullPhysicalResidualTerm f hK threshold (Q i) (B i) (W₁ i)
            output houtput.continuous hob hib (T i) (Sum.inr (), reflected))
        HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
          (restrictionSobolevScale U F hU) ρ
          (fun i ↦ (localRetardedOperator hU U
            (if backward then (Ps i).adjoint else Ps i)).toLinearMap) := by
  intro P
  let S := fun i ↦ (sourceCutMultiplier output houtput.continuous hob).comp
    (ellipticResidual f hK threshold (Q i) (B i))
  have hρ i : 1 ≤ ρ i := (hL i).trans (hLρ i)
  obtain ⟨C, hC, hb⟩ := EllipticLocalization.exists_commonOutput_elliptic_polynomial_fourier_constants
    f hK hΩ hRQΩ output houtput hoc hob AQ AB hAQ hAB
  have hraw i n V (hV : V = S i ∨ V = (S i).adjoint) :=
    hb Rstar hRstar (L i) (ρ i) (hL i) (hLρ i) threshold ht
      (Q i) (B i) (hQ i) (hB i) (hmap i) (hQl i) (hBl i) (hQp i) (hBp i)
      n (ellipticResidual f hK threshold (Q i) (B i)) (Or.inr rfl) V hV
  have hfourier (rev : Bool) :
      HasPolynomialSobolevCost vectorFourierSobolevScale vectorFourierSobolevScale ρ
        (fun i ↦ (if rev then (S i).adjoint else S i).toLinearMap.restrictScalars ℝ) := by
    intro n
    refine ⟨n, (n+2*(d+2) : ℕ), C n, hC n, ?_⟩
    intro i u hu
    let V := if rev then (S i).adjoint else S i
    obtain ⟨hm, hn⟩ := hraw i n V (by cases rev <;> simp [V]) u hu
    refine ⟨hm, ?_⟩
    change vectorFourierSobolevScale.gradeNorm n (V u) ≤ _
    simpa only [vectorFourierSobolevScale_gradeNorm n hm,
      vectorFourierSobolevScale_gradeNorm n hu, Real.rpow_natCast] using hn
  have he i : selectedFullPairedResidualTerm f hK threshold (Q i) (B i) (W₁ i)
      output houtput.continuous hob hib (T i) (Sum.inr ()) = normalizedPair (S i) := by
    rw [selectedFullPairedResidualTerm_elliptic]
  have hsigned i reflected : selectedFullPhysicalResidualTerm f hK threshold (Q i) (B i) (W₁ i)
      output houtput.continuous hob hib (T i) (Sum.inr (), reflected) =
        (if reflected then boundedConjugate ((1/2 : ℂ) • S i) else (1/2 : ℂ) • S i) := rfl
  simpa only [P, he, hsigned] using measured_normalizedPair_and_signed_hasPolynomialRestrictionCost
    ρ hρ S hfourier μ ν hμ hν hμc hνc hμb hνb U hU hνU hμU backward

/-- The original paired estimate is retained as a projection of the same
signed-family estimate (`app:ch_regular:lem:finite-chain`). -/
theorem selectedFullPairedResidualTerm_elliptic_measured_hasPolynomialRestrictionCost
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (output : E → ℝ) (houtput : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1)
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
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (U : Set E) (hU : MeasurableSet U)
    (hνU : tsupport ν ⊆ U) (hμU : tsupport μ ⊆ U) (backward : Bool) :
    let P := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (selectedFullPairedResidualTerm f hK threshold (Q i) (B i) (W₁ i)
        output houtput.continuous hob hib (T i) (Sum.inr ()))
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ
      (fun i ↦ (localRetardedOperator hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) ∧
    HasPolynomialSobolevCost (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale U RF hU) ρ
      (fun i ↦ (localRealCompression hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) := by
  have h := selectedFullPairedResidualTerm_elliptic_measured_hasPolynomialRestrictionCost_with_signed
    f hK hΩ hRQΩ output houtput hoc hob AQ AB hAQ hAB
      ρ L hL hLρ Rstar hRstar threshold ht Q B hQ hB hmap hQl hBl hQp hBp W₁ hib T
      μ ν hμ hν hμc hνc hμb hνb U hU hνU hμU backward
  exact ⟨h.1, h.2.1⟩

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
