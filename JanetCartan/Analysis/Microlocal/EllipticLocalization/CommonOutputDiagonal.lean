module

public import JanetCartan.Analysis.Microlocal.EllipticLocalization.DiagonalProfiles
public import JanetCartan.Analysis.Microlocal.EllipticLocalization.CommonOutput
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PairedDiagonal

/-!
# Diagonal leakage for the literal common-output elliptic factors

The symbol grades, supports and literal regularizations are produced for the
same inverse, complete residual and source. The existing diagonal theorem is
specialized through its purely algebraic first-symbol slot; no characteristic
chart is assumed. The actual `1/i` normalizations and literal adjoints remain.
Consumer: finite mixed-word leakage in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option synthInstance.maxSize 256
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.RegularSector.Realization
namespace JanetCartan.RegularSector.EllipticLocalization
open FiniteMasks.ActualFamily EllipticComplement Characteristic.EvolutionIntegral
open Characteristic.RetardedLocalization
open Realization
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
local notation "χo" => fun y ↦ (f.outputMask y : ℂ)
local notation "χs" => fun z ↦ (f.inputMask z : ℂ)

/-- Actual global elliptic leakage for the solver, full residual and source,
with the supplied common output, complex conjugate pairing and real compression, in either literal
orientation. All analytic inputs to the diagonal theorem are instantiated
from the original coefficient profiles and actual regularization producers.
The supplied buffered proof masks and their representatives belong to the
parent's original localization geometry. Constants precede the varying fields,
slow scale, frequency and accuracy (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`, `measured-adjoint`). -/
theorem exists_commonOutput_elliptic_weighted_restriction_bound
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (output : E → ℝ) (houtput : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    (threshold : ℝ) (ht : f.radialThreshold ≤ threshold)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k)
    {ι ιu ιz : Type*} [Fintype ι] [Fintype ιu] [Fintype ιz]
    (e : Module.Basis ι ℝ (JointVariables E))
    (eu : OrthonormalBasis ιu ℝ E) (ez : OrthonormalBasis ιz ℝ E)
    (backward : Bool) (m : ℕ) {a b : ℝ} (ha : 0 < a)
    (mi mo : LocalizerSymbol (d+1)) {Ki Ii Ko Oo : Set (E × E)}
    (hi : IsBufferedLocalizer mi Ki Ii) (ho : IsBufferedLocalizer mo Ko Oo)
    (hKo : IsCompact Ko) (hdiag : tsupport mi ⊆ Ko)
    (hieven : ∀ y ξ, mi (y, -ξ) = mi (y, ξ))
    (hoeven : ∀ y ξ, mo (y, -ξ) = mo (y, ξ))
    (hiAnn : ∀ p ∈ tsupport mi, p.2 ∈ frequencyAnnulus a b)
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (hplateau : ∀ y ∈ leakageOutputCarrier backward
      (tsupport (fun y ↦ (output y : ℂ)) ×ˢ tsupport (χs)) (Prod.fst '' tsupport mo), ψ y = 1) :
    let O : H →L[ℂ] H := sourceCutMultiplier output houtput.continuous hob
    ∃ (bLoss : Fin 3 → ℕ) (Cmq Creal : Fin 3 → ℕ → ℝ),
      (∀ j N, 0 ≤ Cmq j N) ∧ (∀ j N, 0 ≤ Creal j N) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ ρ L : ℝ, 1 ≤ L → L ≤ ρ →
      ∀ Mi Mo : H →L[ℂ] H,
        (∀ u : H, Mi u =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (rightLocalizer ρ mi (fun z ↦ (u z).ofLp) y)) →
        (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
          fun y ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun z ↦ (u z).ofLp) y)) →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M →
        cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ (j : Fin 3) (z : ℂ) (N : ℕ) (U : Set E) (hU : MeasurableSet U),
        let P := O.comp (![ellipticSolver f hK threshold Q,
          ellipticResidual f hK threshold Q B, ellipticSourcePDO f hK threshold] j)
        let T := if backward then (z • P).adjoint else z • P
        (∀ u : H,
          restrictL2 U ((1 - Mo) ((T + boundedConjugate T) (Mi u))) ∈
            (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU).level m ∧
          (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU).gradeNorm m
            (restrictL2 U ((1 - Mo) ((T + boundedConjugate T) (Mi u)))) ≤
              Cmq j N * ‖z‖ * ρ ^ ((m : ℝ) + (3*(d+1) : ℕ)) *
                L ^ bLoss j * (L/ρ)^N * ‖u‖) ∧
        ∀ u : Lp (EuclideanSpace ℝ (Fin (d+1))) 2 (volume : Measure E),
          let v := l2RealPart (volume.restrict U)
            (restrictL2 U ((1 - Mo) ((T + boundedConjugate T) (Mi (l2ComplexInclusion volume u)))))
          v ∈ (restrictionSobolevScale U (EuclideanSpace ℝ (Fin (d+1))) hU).level m ∧
          (restrictionSobolevScale U (EuclideanSpace ℝ (Fin (d+1))) hU).gradeNorm m v ≤
            Creal j N * ‖z‖ * ρ ^ ((m : ℝ) + (3*(d+1) : ℕ)) *
              L ^ bLoss j * (L/ρ)^N * ‖u‖ := by
  intro O
  obtain ⟨D, _, _, _, _, hin, hout, hgrades⟩ := exists_elliptic_masked_diagonal_profiles f hK
    hΩ hball (fun y ↦ (output y : ℂ)) (Complex.ofRealCLM.contDiff.comp houtput)
    (hoc.comp_left Complex.ofReal_zero) (commonOutput_elliptic_carrier f output hoc hos).2
    threshold ht (b := b) ha AQ AB hAQ hAB mi mo hi ho
  let order : Fin 3 → ℝ := ![-1, -1, 0]
  choose bLoss Cmq Creal hCmq hCreal hbound using fun j : Fin 3 ↦
    exists_weightedPhysicalPDO_restriction_bound e eu ez backward (order j) m ha
      (fun y ↦ (output y : ℂ)) (χs) (hoc.comp_left Complex.ofReal_zero)
      (f.inputMask_compact.comp_left Complex.ofReal_zero)
      mi mo hi.smooth hi.compactSupport hi.range ho hKo hdiag hieven hoeven hiAnn
      J hJ ψ hψ hsψ hplateau D
  refine ⟨bLoss, Cmq, Creal, hCmq, hCreal, ?_⟩
  intro Rstar hR ρ L hL hLρ Mi Mo hMi hMo Q B hQ hB hmap hQl hBl hQp hBp j z N U hU P T
  let c := ![ellipticInverseSymbol f hK threshold Q,
    ellipticResidualSymbol f hK threshold Q B, ellipticSourceSymbol f hK threshold] j
  have hc : c ∈ ({ellipticInverseSymbol f hK threshold Q,
      ellipticResidualSymbol f hK threshold Q B, ellipticSourceSymbol f hK threshold} :
      Set (E → E → CMat)) := by fin_cases j <;> simp [c]
  obtain ⟨hsm, Preg, _, hreal, hlim⟩ := exists_commonOutput_ellipticPDO_oriented_regularizations f hK
    hΩ hball output houtput hoc hos hob ht Q B hQ hB hmap hQl hBl c hc
  have hmasked := commonOutput_ellipticPDO_eq_masked f hK hΩ hball output houtput hos hob
    ht Q B hQ hB hmap hQl hBl c hc
  simp only [hmasked] at hlim
  have hfreq := elliptic_masked_amplitude_support f hK (fun y ↦ (output y : ℂ))
    (zero_lt_one.trans_le (f.radialThreshold_ge_one.trans ht)) Q B
  have hg := hgrades Rstar hR L ρ hL (hL.trans hLρ) Q B hQ hB hmap
    ((cNorm_mono_order (by omega : 1 ≤ 2*(d+2)+2)).trans hQl)
    ((cNorm_mono_order (Nat.zero_le _)).trans hBl) hQp hBp backward j
  have hcall := hbound j ρ L hL hLρ Mi Mo hMi hMo
    (0 : E → Fin (d+1) → CMat) (0 : E → CMat) (0 : TwoTimeAmplitude d (d+1)) c
    (fun _ _ ↦ 1) (fun _ ↦ 1) 0
  have hec : directPDOSymbols (0 : E → Fin (d+1) → CMat) (0 : E → CMat)
      (0 : TwoTimeAmplitude d (d+1)) c (fun _ _ ↦ 1) (fun _ ↦ 1) 0 = c := by
    funext y ξ
    simp [directPDOSymbols, directAlgebraicSymbol]
  rw [hec] at hcall
  have hp := hcall (hsm backward) hg.1 (fun y _ k v _ ↦ hin L hL y k v) hg.2
    (hout L hL) (tsupport (ellipticSourceMask f hK threshold)) hfreq.1 hfreq.2.1
    (fun y z ξ hξ ↦ hfreq.2.2.2 c hc backward y z ξ (Or.inr hξ))
    complexPhysicalCutoff (fun _ _ _ ↦ rfl) (Preg backward) (hreal backward) (hlim backward)
  let scalar : Fin 3 → ℂ := ![1/Complex.I, 1/Complex.I, 1]
  have hbase : ![ellipticSolver f hK threshold Q, ellipticResidual f hK threshold Q B,
      ellipticSourcePDO f hK threshold] j = scalar j • maskedPhysicalPDO (χo) (χs) c := by
    fin_cases j <;> simp [c, scalar, ellipticSolver, ellipticResidual, ellipticSourcePDO]
  have hP : P = scalar j • maskedPhysicalPDO (fun y ↦ (output y : ℂ)) (χs) c := by
    dsimp only [P]
    rw [hbase, ContinuousLinearMap.comp_smul]
    exact congrArg (fun T ↦ scalar j • T) hmasked
  have he : z • P = (z * scalar j) • maskedPhysicalPDO (fun y ↦ (output y : ℂ)) (χs) c := by rw [hP, smul_smul]
  have hn : ‖z * scalar j‖ = ‖z‖ := by fin_cases j <;> simp [scalar]
  have hord : max 0 (order j) = 0 := by fin_cases j <;> norm_num [order]
  simpa only [← he, hn, hord, zero_add] using hp (z * scalar j) N U hU

end JanetCartan.RegularSector.EllipticLocalization
