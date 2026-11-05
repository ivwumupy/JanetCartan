module

public import JanetCartan.Analysis.Microlocal.EllipticLocalization.PolynomialCosts
public import JanetCartan.Analysis.Microlocal.EllipticLocalization.CommonOutput

/-!
# Common-output elliptic factors on the original Sobolev scales

The supplied interior plateau is the parent's original proof localizer.
Applying the produced symbol budgets to the existing restriction estimate
retains zero extension, the original physical masks, and literal adjunction
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticLocalization
open FiniteMasks.ActualFamily EllipticComplement Characteristic.PdoRealization
open Characteristic.EvolutionIntegral Characteristic.RetardedLocalization
open ArbitraryAccuracy.ResidualLocalization FourierIntegral FourierIntegral.LowBounds AmplitudeBound
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

/-- Both actual `1/i`-normalized elliptic operators have polynomial
restriction costs in both literal orientations. The original coefficient
profiles produce every analytic input to the PDO estimate; the only extra
input is the parent's fixed geometric plateau (`app:ch_regular:eq:chain-tail`). -/
theorem commonOutput_ellipticOperators_hasPolynomialRestrictionCost
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
    (residual backward : Bool) {xχ : E} (χ : ContDiffBump xχ)
    (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hs : tsupport (χ : E → ℝ) ⊆ U)
    (hp : ∀ y ∈ tsupport (if backward then (fun y ↦ (output y : ℂ)) else (χs)), χ y = 1) :
    let O : H →L[ℂ] H := sourceCutMultiplier output houtput.continuous hob
    let T := fun i ↦ O.comp (if residual then ellipticResidual f hK threshold (Q i) (B i)
      else ellipticSolver f hK threshold (Q i))
    HasPolynomialSobolevCost (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU)
      (restrictionSobolevScale V (EuclideanSpace ℂ (Fin (d+1))) hV) ρ
      (fun i ↦ (localRetardedOperator hU V
        (if backward then (T i).adjoint else T i)).toLinearMap) := by
  intro O T
  obtain ⟨R, _, N, _, C, hC, hb⟩ := exists_elliptic_masked_profile_budgets f hK hΩ hRQΩ
    (fun y ↦ (output y : ℂ)) (Complex.ofRealCLM.contDiff.comp houtput) (hoc.comp_left Complex.ofReal_zero)
    (commonOutput_elliptic_carrier f output hoc hos).2 AQ AB hAQ hAB
  let c i := if residual then ellipticResidualSymbol f hK threshold (Q i) (B i)
    else ellipticInverseSymbol f hK threshold (Q i)
  have hc i : c i ∈ ({ellipticInverseSymbol f hK threshold (Q i),
      ellipticResidualSymbol f hK threshold (Q i) (B i)} : Set (E → E → CMat)) := by
    cases residual <;> simp [c]
  have hbud i := hb Rstar hRstar (L i) (hL i) threshold ht (Q i) (B i)
    (hQ i) (hB i) (hmap i) (hQl i) (hBl i) (hQp i) (hBp i) (c i) (hc i)
  have hhi n i ξ is (hi : is.length ≤ 2*(d+1+1)+n) z :
      ‖matrixAmplitudeCoordinateDerivList is
        (maskedPhysicalPDOCycleSymbol (fun y ↦ (output y : ℂ)) (χs) (c i) ξ) z‖ ≤
          C (2*(d+2)+n) * L i ^ (n+2*(d+2)) := by
    have hh := (le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg ξ])).trans
      ((hbud i).2 (2*(d+2)+n) ξ is hi z)
    simpa only [Nat.add_comm n (2*(d+2))] using hh
  have hr := maskedPhysicalPDO_hasPolynomialRestrictionCost ρ L hL hLρ (fun y ↦ (output y : ℂ)) (χs) c R N
    (fun i ↦ (hbud i).1) (2*(d+2)) (fun n ↦ C (2*(d+2)+n))
    (fun n ↦ hC _) hhi backward χ U V hU hV hs hp
  let P i := maskedPhysicalPDO (fun y ↦ (output y : ℂ)) (χs) (c i)
  have hbase i : (if residual then ellipticResidual f hK threshold (Q i) (B i)
      else ellipticSolver f hK threshold (Q i)) =
        (1/Complex.I) • maskedPhysicalPDO (χo) (χs) (c i) := by cases residual <;> rfl
  have he i : T i = (1/Complex.I) • P i := by
    have hmasked := commonOutput_ellipticPDO_eq_masked f hK hΩ hRQΩ output houtput hos hob
      ht (Q i) (B i) (hQ i) (hB i) (hmap i) (hQl i) (hBl i) (c i)
      (by cases residual <;> simp [c])
    dsimp only [T, O, P]
    rw [hbase, ContinuousLinearMap.comp_smul, hmasked]
  cases backward with
  | false =>
    simpa only [Bool.false_eq_true, ↓reduceIte, he] using
      localOperator_smul_hasPolynomialRestrictionCost ρ
        (fun i ↦ zero_lt_one.trans_le ((hL i).trans (hLρ i))) P (1/Complex.I) U V hU hV hr
  | true =>
    simpa only [↓reduceIte, he, map_smulₛₗ] using
      localOperator_smul_hasPolynomialRestrictionCost ρ
        (fun i ↦ zero_lt_one.trans_le ((hL i).trans (hLρ i)))
        (fun i ↦ (P i).adjoint) ((starRingEnd ℂ) (1/Complex.I)) U V hU hV hr

/-- The SAME principal elliptic source has order-zero Fourier cost, for
every threshold and either literal orientation. No coefficient hypothesis
is needed: all symbol budgets come from its actual masks
(`app:ch_regular_base:eq:sector-theorem-identity`). -/
theorem commonOutput_ellipticSourcePDO_hasPolynomialFourierCost
    (output : E → ℝ) (houtput : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    {ι : Type*} (ρ threshold : ι → ℝ) (hρ : ∀ i, 1 ≤ ρ i) (backward : Bool) :
    HasPolynomialSobolevCost vectorFourierSobolevScale vectorFourierSobolevScale ρ
      (fun i ↦ (if backward then ((sourceCutMultiplier output houtput.continuous hob : H →L[ℂ] H).comp
          (ellipticSourcePDO f hK (threshold i))).adjoint
        else (sourceCutMultiplier output houtput.continuous hob : H →L[ℂ] H).comp
          (ellipticSourcePDO f hK (threshold i))).toLinearMap.restrictScalars ℝ) := by
  have he := commonOutput_ellipticSourcePDO_eq_masked f hK output houtput hos hob
  simp only [he]
  obtain ⟨R, _, C, hC, hb⟩ := exists_ellipticSource_masked_pdo_budgets f hK
    (fun y ↦ (output y : ℂ)) (Complex.ofRealCLM.contDiff.comp houtput) (hoc.comp_left Complex.ofReal_zero)
    (commonOutput_elliptic_carrier f output hoc hos).2
  apply maskedPhysicalPDO_hasPolynomialFourierCost ρ (fun _ ↦ 1) (fun _ ↦ le_rfl) hρ
    (fun y ↦ (output y : ℂ)) (χs) (fun i ↦ ellipticSourceSymbol f hK (threshold i)) R (C (2*(d+2)))
    (fun i ↦ (hb (threshold i)).1) 0 (fun n ↦ C (2*(d+2)+n)) (fun n ↦ hC _) ?_ _ ?_
  · intro n i ξ is hi z
    simpa only [one_pow, mul_one] using (hb (threshold i)).2 (2*(d+2)+n) ξ is hi z
  · intro i
    cases backward <;> simp

/-- The actual principal source, with the supplied restriction plateau and
the original source-before-Fourier order, has polynomial restriction cost
in either literal orientation (`app:ch_regular:lem:finite-chain`). -/
theorem commonOutput_ellipticSourcePDO_hasPolynomialRestrictionCost
    (output : E → ℝ) (houtput : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    {ι : Type*} (ρ threshold : ι → ℝ) (hρ : ∀ i, 1 ≤ ρ i) (backward : Bool)
    {xχ : E} (χ : ContDiffBump xχ) (U V : Set E)
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hs : tsupport (χ : E → ℝ) ⊆ U)
    (hp : ∀ y ∈ tsupport (if backward then (fun y ↦ (output y : ℂ)) else (χs)), χ y = 1) :
    HasPolynomialSobolevCost (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU)
      (restrictionSobolevScale V (EuclideanSpace ℂ (Fin (d+1))) hV) ρ
      (fun i ↦ (localRetardedOperator hU V (if backward then
        ((sourceCutMultiplier output houtput.continuous hob : H →L[ℂ] H).comp
          (ellipticSourcePDO f hK (threshold i))).adjoint
        else (sourceCutMultiplier output houtput.continuous hob : H →L[ℂ] H).comp
          (ellipticSourcePDO f hK (threshold i)))).toLinearMap) := by
  have he := commonOutput_ellipticSourcePDO_eq_masked f hK output houtput hos hob
  simp only [he]
  obtain ⟨R, _, C, hC, hb⟩ := exists_ellipticSource_masked_pdo_budgets f hK
    (fun y ↦ (output y : ℂ)) (Complex.ofRealCLM.contDiff.comp houtput) (hoc.comp_left Complex.ofReal_zero)
    (commonOutput_elliptic_carrier f output hoc hos).2
  apply maskedPhysicalPDO_hasPolynomialRestrictionCost ρ (fun _ ↦ 1) (fun _ ↦ le_rfl) hρ
    (fun y ↦ (output y : ℂ)) (χs) (fun i ↦ ellipticSourceSymbol f hK (threshold i)) R (C (2*(d+2)))
    (fun i ↦ (hb (threshold i)).1) 0 (fun n ↦ C (2*(d+2)+n)) (fun n ↦ hC _)
    ?_ backward χ U V hU hV hs hp
  intro n i ξ is hi z
  simpa only [one_pow, mul_one] using (hb (threshold i)).2 (2*(d+2)+n) ξ is hi z

/-- Uniform polynomial Fourier costs for the actual `1/i`-normalized solver
and full residual, including their literal adjoints. Constants and the fixed
reserve `2*(d+2)` precede all varying fields and scales. The normal and high
symbol estimates are produced here (`app:ch_regular:lem:finite-chain`). -/
theorem exists_commonOutput_elliptic_polynomial_fourier_constants
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (output : E → ℝ) (houtput : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) :
    let O : H →L[ℂ] H := sourceCutMultiplier output houtput.continuous hob
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
      ∀ W : H →L[ℂ] H, (W = O.comp T ∨ W = (O.comp T).adjoint) →
      ∀ u, MemVectorFourierSobolev (n : ℝ) u →
        MemVectorFourierSobolev (n : ℝ) (W u) ∧
        vectorFourierSobolevNorm (n : ℝ) (W u) ≤
          C n * ρ ^ (n + 2*(d+2)) * vectorFourierSobolevNorm (n : ℝ) u := by
  intro O
  obtain ⟨C, hC, hb⟩ := exists_elliptic_polynomial_fourier_constants f hK hΩ hRQΩ AQ AB hAQ hAB
  obtain ⟨D, hD, hd⟩ := FiniteAssembly.exists_outputMask_sobolev_constants (q := d+1)
    output houtput hoc hob
  refine ⟨fun n ↦ D n * C n * D n,
    fun n ↦ mul_nonneg (mul_nonneg (zero_le_one.trans (hD n)) (hC n))
      (zero_le_one.trans (hD n)), ?_⟩
  intro Rstar hR L ρ hL hLρ threshold ht Q B hQ hB hmap hQl hBl hQp hBp n T hT W hW u hu
  have hraw := hb Rstar hR L ρ hL hLρ threshold ht Q B hQ hB hmap hQl hBl hQp hBp n T hT
  have hh := hd T n n (C n * ρ ^ (n+2*(d+2))) 0
    (mul_nonneg (hC n) (pow_nonneg (zero_le_one.trans (hL.trans hLρ)) _)) le_rfl
    (by simpa only [zero_mul, add_zero] using hraw) W hW u hu
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  simp only [zero_mul, add_zero]
  ring

/-- Apply the uniform constants to any original coefficient/history family.
Both actual operators and both literal orientations satisfy the existing
Fourier-cost predicate (`app:ch_regular:eq:chain-tail`). -/
theorem commonOutput_ellipticOperators_hasPolynomialFourierCost
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
    (T W : ι → H →L[ℂ] H)
    (hT : ∀ i, T i ∈ ({ellipticSolver f hK threshold (Q i),
      ellipticResidual f hK threshold (Q i) (B i)} : Set (H →L[ℂ] H)))
    (hW : ∀ i, W i = (sourceCutMultiplier output houtput.continuous hob : H →L[ℂ] H).comp (T i) ∨
      W i = ((sourceCutMultiplier output houtput.continuous hob : H →L[ℂ] H).comp (T i)).adjoint) :
    HasPolynomialSobolevCost vectorFourierSobolevScale vectorFourierSobolevScale ρ
      (fun i ↦ (W i).toLinearMap.restrictScalars ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_commonOutput_elliptic_polynomial_fourier_constants f hK hΩ hRQΩ
    output houtput hoc hob AQ AB hAQ hAB
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
