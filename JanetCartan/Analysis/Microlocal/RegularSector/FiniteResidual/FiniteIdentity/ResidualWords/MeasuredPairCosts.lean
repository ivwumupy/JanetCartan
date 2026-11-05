module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords.EllipticCosts
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Positive

/-!
# Measured costs before and after normalized conjugate pairing

The same Fourier bounds give restriction costs for a normalized pair and each
of its original half-scaled signed letters. The literal adjoint exchanges the
measurement masks. The signed costs feed the complex-word expansion in
`NormalizedResidualWords.measured_realResidual_hchain_of_words`; real compression
is asserted here only for the complete pair (`app:ch_regular:lem:finite-chain`).
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

/-- Apply the actual measured-mask estimate to a proved Fourier cost
(`app:ch_regular:lem:finite-chain`). -/
private theorem measured_cost_of_fourier_cost
    (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (S : ι → H →L[ℂ] H)
    (hS : HasPolynomialSobolevCost vectorFourierSobolevScale vectorFourierSobolevScale
      ρ (fun i ↦ (S i).toLinearMap.restrictScalars ℝ))
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (U : Set E) (hU : MeasurableSet U) (hνU : tsupport ν ⊆ U) :
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ (fun i ↦ (localRetardedOperator hU U
        (measuredOperator μ ν hμ.continuous hν.continuous hμb hνb (S i))).toLinearMap) := by
  intro n
  obtain ⟨t, c, C, hC, hb⟩ := hS n
  obtain ⟨D, hD, hm⟩ := exists_measuredOperator_restriction_tame_constant (q := d+1)
    μ ν hμ hν hμc hνc hμb hνb t n
  refine ⟨t, c, D*C, mul_nonneg (zero_le_one.trans hD) hC, ?_⟩
  intro i u hu
  have hraw v (hv : MemVectorFourierSobolev (t : ℝ) v) := hb i v hv
  have hnorm v (hv : MemVectorFourierSobolev (t : ℝ) v) :
      MemVectorFourierSobolev (n : ℝ) (S i v) ∧
        vectorFourierSobolevNorm (n : ℝ) (S i v) ≤
          (C*ρ i^c)*(vectorFourierSobolevNorm (t : ℝ) v+0*‖v‖) := by
    obtain ⟨ha, hn⟩ := hraw v hv
    change MemVectorFourierSobolev (n : ℝ) (S i v) at ha
    refine ⟨ha, ?_⟩
    change vectorFourierSobolevScale.gradeNorm n (S i v) ≤ _ at hn
    simpa only [vectorFourierSobolevScale_gradeNorm n ha,
      vectorFourierSobolevScale_gradeNorm t hv, zero_mul, add_zero] using hn
  obtain ⟨ha, hn⟩ := hm (S i) (C*ρ i^c) 0
    (mul_nonneg hC (Real.rpow_nonneg (hρ i).le _)) le_rfl hnorm U U hU hνU u hu
  refine ⟨ha, ?_⟩
  change (restrictionSobolevScale U F hU).gradeNorm n
    (localRetardedOperator hU U (measuredOperator μ ν hμ.continuous hν.continuous hμb hνb (S i)) u) ≤ _
  rw [restrictionSobolevScale_gradeNorm hU ha, restrictionSobolevScale_gradeNorm hU hu]
  simpa only [zero_mul, add_zero, mul_assoc] using hn

/-- The external half and literal conjugate preserve the actual measured
polynomial cost and its real compression (`measured-adjoint`, `chain-tail`). -/
theorem measured_normalizedPair_and_signed_hasPolynomialRestrictionCost
    (ρ : ι → ℝ) (hρ : ∀ i, 1 ≤ ρ i) (S : ι → H →L[ℂ] H)
    (hS : ∀ backward : Bool,
      HasPolynomialSobolevCost vectorFourierSobolevScale vectorFourierSobolevScale ρ
        (fun i ↦ (if backward then (S i).adjoint else S i).toLinearMap.restrictScalars ℝ))
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (U : Set E) (hU : MeasurableSet U) (hνU : tsupport ν ⊆ U)
    (hμU : tsupport μ ⊆ U) (backward : Bool) :
    let P := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (normalizedPair (S i))
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
          (if reflected then boundedConjugate ((1/2 : ℂ) • S i) else (1/2 : ℂ) • S i)
        HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
          (restrictionSobolevScale U F hU) ρ
          (fun i ↦ (localRetardedOperator hU U
            (if backward then (Ps i).adjoint else Ps i)).toLinearMap) := by
  intro P
  let A := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb (S i)
  have hpos i : 0 < ρ i := zero_lt_one.trans_le (hρ i)
  have hcost : HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ (fun i ↦ (localRetardedOperator hU U
        (if backward then (A i).adjoint else A i)).toLinearMap) := by
    cases backward with
    | false =>
      exact measured_cost_of_fourier_cost ρ hpos S (hS false)
        μ ν hμ hν hμc hνc hμb hνb U hU hνU
    | true =>
      simpa only [ite_true, A, measuredOperator_adjoint] using
        measured_cost_of_fourier_cost ρ hpos (fun i ↦ (S i).adjoint) (hS true)
          ν μ hν hμ hνc hμc hνb hμb U hU hμU
  have he i : P i = normalizedPair (A i) := by
    dsimp only [P]
    rw [normalizedPair, ← physicalPair_measuredOperator]
    congr 1
    funext _
    simp only [measuredOperator, A, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.smul_comp]
  have hscaled := localOperator_smul_hasPolynomialRestrictionCost ρ hpos
    (fun i ↦ if backward then (A i).adjoint else A i) (1/2 : ℂ) U U hU hU hcost
  have hpaired := physicalPairedSectorSum_hasPolynomialRestrictionCost ρ hρ
    (fun _ : Unit ↦ fun i ↦ (1/2 : ℂ) • (if backward then (A i).adjoint else A i))
    {()} U U hU hU (fun _ _ ↦ hscaled)
  have hc : HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ (fun i ↦ (localRetardedOperator hU U
        (if backward then (P i).adjoint else P i)).toLinearMap) := by
    cases backward with
    | false => simpa only [Bool.false_eq_true, ↓reduceIte, he, normalizedPair] using hpaired
    | true => simpa only [ite_true, he, normalizedPair, physicalPairedSectorSum_adjoint_eq,
        map_smulₛₗ, map_div₀, map_one, map_ofNat] using hpaired
  refine ⟨hc, realCompression_hasPolynomialRestrictionCost ρ hpos _ U U hU hU hc, ?_⟩
  intro reflected Ps
  have hscaledDir i :
      (if backward then
        (measuredOperator μ ν hμ.continuous hν.continuous hμb hνb ((1/2 : ℂ) • S i)).adjoint
        else measuredOperator μ ν hμ.continuous hν.continuous hμb hνb ((1/2 : ℂ) • S i)) =
        (1/2 : ℂ) • (if backward then (A i).adjoint else A i) := by
    have heq : measuredOperator μ ν hμ.continuous hν.continuous hμb hνb ((1/2 : ℂ) • S i) =
        (1/2 : ℂ) • A i := by
      simp only [measuredOperator, A, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
    rw [heq]
    cases backward <;> simp only [Bool.false_eq_true, ↓reduceIte, map_smulₛₗ,
      map_div₀, map_one, map_ofNat]
  have hcj := boundedConjugate_hasPolynomialRestrictionCost ρ hpos
    (fun i ↦ (1/2 : ℂ) • (if backward then (A i).adjoint else A i)) U U hU hU hscaled
  cases reflected with
  | false => simpa only [Ps, Bool.false_eq_true, ↓reduceIte, hscaledDir] using hscaled
  | true =>
    dsimp only [Ps]
    simp only [ite_true, ← boundedConjugate_measuredOperator, boundedConjugate_adjoint]
    have heq i : (if backward then boundedConjugate
        (measuredOperator μ ν hμ.continuous hν.continuous hμb hνb ((1/2 : ℂ) • S i)).adjoint
        else boundedConjugate
        (measuredOperator μ ν hμ.continuous hν.continuous hμb hνb ((1/2 : ℂ) • S i))) =
        boundedConjugate ((1/2 : ℂ) • (if backward then (A i).adjoint else A i)) := by
      rw [← hscaledDir]
      cases backward <;> rfl
    simpa only [heq] using hcj


end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
