module

public import JanetCartan.Analysis.Microlocal.EllipticComplement.SymbolBudgets
public import JanetCartan.Analysis.Microlocal.EllipticLocalization.MaskedBudgets
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.OperatorBounds
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.PdoRestriction
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Pairing

/-!
# Polynomial costs of the actual elliptic PDOs

The original coefficient profiles supply the high symbol budgets, with the
normal-amplitude certificates constructed by `EllipticComplement`. The same
physical-frequency conversion and both masks feed the existing Fourier and
restriction estimates of `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticLocalization
open FiniteMasks.ActualFamily EllipticComplement Characteristic.PdoRealization
open Characteristic.EvolutionIntegral FiniteAssembly Characteristic.RetardedLocalization
open ArbitraryAccuracy.ResidualLocalization FourierIntegral AmplitudeBound
open Pseudodifferential ResponseTransfer LocalSobolev
open CharacteristicTransport.CompleteResidual ResponseTransfer.Complement
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
local notation "H" => SpacetimeL2 d (d+1)
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
local notation "χo" => fun y ↦ (f.outputMask y : ℂ)
local notation "χs" => fun z ↦ (f.inputMask z : ℂ)

/-- Produce the literal normal-amplitude certificate and all coordinate
budgets from the original coefficient profiles. The weight still has degree
minus one, the slow-scale offset is zero, and the constants precede all
fields, scales and thresholds (`app:ch_regular:eq:high-amplitude`). -/
theorem exists_elliptic_masked_profile_budgets
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (χout : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hco : HasCompactSupport χout)
    (hsout : tsupport χout ⊆ closedBall x (2*f.physicalRadius))
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) :
    ∃ R > 0, ∃ N > 0, ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
      ∀ threshold ≥ f.radialThreshold, ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M →
        cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ s ∈ ({ellipticInverseSymbol f hK threshold Q,
        ellipticResidualSymbol f hK threshold Q B} : Set (E → E → CMat)),
        GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout (χs) s) R N ∧
        ∀ k ξ is, is.length ≤ k → ∀ z,
          (1+‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
            (maskedPhysicalPDOCycleSymbol χout (χs) s ξ) z‖ ≤ C k * L ^ k := by
  obtain ⟨R, hR, N, hN, D, hD, hb⟩ := exists_elliptic_masked_pdo_budgets f hK hΩ hRQΩ
    χout ho hco hsout
  let C k := D k * (1+AQ (k+1)+AB (k+1))
  refine ⟨R, hR, N, hN, C,
    fun k ↦ mul_nonneg (hD k).le (by linarith [hAQ (k+1), hAB (k+1)]), ?_⟩
  intro Rstar hRstar L hL threshold ht Q B hQ hB hmap hQl hBl hQp hBp s hs
  obtain ⟨hn, _, hj⟩ := hb threshold ht Q B hQ hB hmap hQl hBl s hs
  refine ⟨hn, ?_⟩
  intro k ξ is hi z
  have hp : L ^ (k+1-Rstar) ≤ L ^ k := pow_le_pow_right₀ hL (by omega)
  have hq := (hQp (k+1)).trans (mul_le_mul_of_nonneg_left hp (hAQ _))
  have hb' := (hBp (k+1)).trans (mul_le_mul_of_nonneg_left hp (hAB _))
  have hcoeff : 1+cNorm (closedBall x RQ) (k+1) Q+cNorm (closedBall x RQ) (k+1) B ≤
      (1+AQ (k+1)+AB (k+1)) * L ^ k := by
    nlinarith [one_le_pow₀ hL (n := k)]
  exact (hj k ξ is hi z).trans ((mul_le_mul_of_nonneg_left hcoeff (hD k).le).trans_eq
    (by dsimp only [C]; ring))

/-- Produce the literal normal-amplitude certificate and all coordinate
budgets from the original coefficient profiles. The weight still has degree
minus one, the slow-scale offset is zero, and the constants precede all
fields, scales and thresholds (`app:ch_regular:eq:high-amplitude`). -/
theorem exists_ellipticPDO_profile_budgets
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) :
    ∃ R > 0, ∃ N > 0, ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
      ∀ threshold ≥ f.radialThreshold, ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M →
        cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ s ∈ ({ellipticInverseSymbol f hK threshold Q,
        ellipticResidualSymbol f hK threshold Q B} : Set (E → E → CMat)),
        GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol (χo) (χs) s) R N ∧
        ∀ k ξ is, is.length ≤ k → ∀ z,
          (1+‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
            (maskedPhysicalPDOCycleSymbol (χo) (χs) s ξ) z‖ ≤ C k * L ^ k := by
  exact exists_elliptic_masked_profile_budgets f hK hΩ hRQΩ (χo)
    (Complex.ofRealCLM.contDiff.comp f.outputMask_smooth)
    (f.outputMask_compact.comp_left Complex.ofReal_zero) (elliptic_physical_carrier f).2.1
    AQ AB hAQ hAB

/-- Uniform polynomial Fourier costs for the actual `1/i`-normalized solver
and full residual, including their literal adjoints. Constants and the fixed
reserve `2*(d+2)` precede all varying fields and scales. The normal and high
symbol estimates are produced here (`app:ch_regular:lem:finite-chain`). -/
theorem exists_elliptic_polynomial_fourier_constants
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → L ≤ ρ →
      ∀ threshold ≥ f.radialThreshold, ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M →
        cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ n : ℕ, ∀ T ∈ ({ellipticSolver f hK threshold Q,
        ellipticResidual f hK threshold Q B} : Set (H →L[ℂ] H)),
      ∀ W : H →L[ℂ] H, (W = T ∨ W = T.adjoint) →
      ∀ u, MemVectorFourierSobolev (n : ℝ) u →
        MemVectorFourierSobolev (n : ℝ) (W u) ∧
        vectorFourierSobolevNorm (n : ℝ) (W u) ≤
          C n * ρ ^ (n + 2*(d+2)) * vectorFourierSobolevNorm (n : ℝ) u := by
  obtain ⟨R, _, N, _, D, hD, hb⟩ := exists_ellipticPDO_profile_budgets f hK hΩ hRQΩ AQ AB hAQ hAB
  choose C hC hcost using fun n ↦ exists_maskedPhysicalPDO_polynomial_fourier_constant
    (d := d) (q := d+1) R N n (2*(d+2)) (D (2*(d+2)+n)) (hD _)
  refine ⟨C, hC, ?_⟩
  intro Rstar hR L ρ hL hLρ threshold ht Q B hQ hB hmap hQl hBl hQp hBp n T hT W hW u hu
  have hraw (s : E → E → CMat)
      (hs : s ∈ ({ellipticInverseSymbol f hK threshold Q,
        ellipticResidualSymbol f hK threshold Q B} : Set (E → E → CMat))) :
      ∀ V : H →L[ℂ] H, (V = maskedPhysicalPDO (χo) (χs) s ∨
        V = (maskedPhysicalPDO (χo) (χs) s).adjoint) → ∀ v,
        MemVectorFourierSobolev (n : ℝ) v → MemVectorFourierSobolev (n : ℝ) (V v) ∧
        vectorFourierSobolevNorm (n : ℝ) (V v) ≤
          (C n * ρ ^ (n+2*(d+2))) * (vectorFourierSobolevNorm (n : ℝ) v + 0*‖v‖) := by
    obtain ⟨hn, hj⟩ := hb Rstar hR L hL threshold ht Q B hQ hB hmap hQl hBl hQp hBp s hs
    have hhi ξ is (hi : is.length ≤ 2*(d+1+1)+n) z :
        ‖matrixAmplitudeCoordinateDerivList is (maskedPhysicalPDOCycleSymbol (χo) (χs) s ξ) z‖ ≤
          D (2*(d+2)+n) * L ^ (n+2*(d+2)) := by
      have hh := (le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg ξ])).trans
        (hj (2*(d+2)+n) ξ is hi z)
      simpa only [Nat.add_comm n (2*(d+2))] using hh
    simpa only [zero_mul, add_zero] using hcost n ρ L hL hLρ (χo) (χs) s hn hhi
  have hnorm : ‖(1 / Complex.I : ℂ)‖ = 1 := by simp
  rcases hT with hT | hT
  · rw [hT] at hW
    simpa only [zero_mul, add_zero] using direct_sobolev_unit_smul _ (1/Complex.I) hnorm
      (n : ℝ) (n : ℝ) (C n * ρ^(n+2*(d+2))) 0 (hraw _ (Or.inl rfl)) W hW u hu
  · change T = ellipticResidual f hK threshold Q B at hT
    rw [hT] at hW
    simpa only [zero_mul, add_zero] using direct_sobolev_unit_smul _ (1/Complex.I) hnorm
      (n : ℝ) (n : ℝ) (C n * ρ^(n+2*(d+2))) 0 (hraw _ (Or.inr rfl)) W hW u hu

/-- Apply the uniform constants to any original coefficient/history family.
Both actual operators and both literal orientations satisfy the existing
Fourier-cost predicate (`app:ch_regular:eq:chain-tail`). -/
theorem ellipticOperators_hasPolynomialFourierCost
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
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
    (T W : ι → H →L[ℂ] H)
    (hT : ∀ i, T i ∈ ({ellipticSolver f hK threshold (Q i),
      ellipticResidual f hK threshold (Q i) (B i)} : Set (H →L[ℂ] H)))
    (hW : ∀ i, W i = T i ∨ W i = (T i).adjoint) :
    HasPolynomialSobolevCost vectorFourierSobolevScale vectorFourierSobolevScale ρ
      (fun i ↦ (W i).toLinearMap.restrictScalars ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_elliptic_polynomial_fourier_constants f hK hΩ hRQΩ AQ AB hAQ hAB
  intro n
  refine ⟨n, (n+2*(d+2) : ℕ), C n, hC n, ?_⟩
  intro i u hu
  obtain ⟨hm, hn⟩ := hb Rstar hRstar (L i) (ρ i) (hL i) (hLρ i) threshold ht
    (Q i) (B i) (hQ i) (hB i) (hmap i) (hQl i) (hBl i) (hQp i) (hBp i)
    n (T i) (hT i) (W i) (hW i) u hu
  refine ⟨hm, ?_⟩
  change vectorFourierSobolevScale.gradeNorm n (W i u) ≤ _
  rw [vectorFourierSobolevScale_gradeNorm n hm, vectorFourierSobolevScale_gradeNorm n hu,
    Real.rpow_natCast]
  exact hn

end JanetCartan.RegularSector.EllipticLocalization
