module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords.UniformMeasuredEllipticLeakage

/-!
# Elliptic leakage on the retained even proof masks

The fixed compact base, buffer and joint mask profile determine the constants
before all varying proof masks. Both physical measurements stay inside every
half-scaled complex letter.
Literal adjoints and whole conjugates use the same actual elliptic residual.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option synthInstance.maxSize 256
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.RegularSector.Realization
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteResidual.FiniteIdentity
open FiniteMasks.ActualFamily EllipticComplement Characteristic.EvolutionIntegral
open Characteristic.RetardedLocalization Realization
open ArbitraryAccuracy.ResidualLocalization ArbitraryAccuracy.EvolutionLocalization
open CharacteristicTransport.CompleteResidual FourierIntegral
open FullLowBounds LowBounds LowBounds.FrequencyCutoff
open FiniteChain.Graph KernelLimits KernelEstimates
open PhysicalShells PhysicalShells.Comparable PhysicalShells.Noncomparable
open KernelEstimates.NoncomparableGeometry
open Pseudodifferential ResponseTransfer LocalSobolev FiniteAssembly
open ArbitraryAccuracy.SelectedLocalization ArbitraryAccuracy.SelectedEvenProofMasks
variable {d : ℕ}
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- Apply the actual uniform elliptic estimate to prescribed even masks.
A common physical plateau is constructed before the coefficient fields and
masks vary. The exact normalized elliptic letter retains both measurements,
the external half, whole conjugation and literal adjoint. Consumer: all
elliptic factors of `finiteChain_observation_rapidDecayAt.hleak`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_prescribed_measured_elliptic_leakage_constants
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (output : Euclidean (d+1) → ℝ) (houtput : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    (threshold : ℝ) (ht : f.radialThreshold ≤ threshold)
    (μ ν : Euclidean (d+1) → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k)
    {ι ιu ιz : Type*} [Fintype ι] [Fintype ιu] [Fintype ιz]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean (d+1))))
    (eu : OrthonormalBasis ιu ℝ (Euclidean (d+1))) (ez : OrthonormalBasis ιz ℝ (Euclidean (d+1)))
    (backward : Bool) (m : ℕ) {a b : ℝ} (ha : 0 < a)
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] (Euclidean (d+1)))
    (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)
    (Rbase : ℝ) (Hmask : ℕ → ℝ) (hHmask : ∀ k, 0 ≤ Hmask k)
    {buffer : ℝ} (hbuffer : 0 < buffer) :
    ∃ (bLoss : ℕ) (Cmq : ℕ → ℝ), (∀ N, 0 ≤ Cmq N) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ ρ L : ℝ, 1 ≤ L → L ≤ ρ →
      ∀ (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
        (B : Euclidean (d+1) → MetricTensor (d+1)),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M →
        cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ (mi mo : LocalizerSymbol (d+1))
        (Ki Oi Ko Oo : Set (Euclidean (d+1) × Euclidean (d+1))),
      IsBufferedLocalizer mi Ki Oi → IsBufferedLocalizer mo Ko Oo →
      (∀ y ξ, mi (y,-ξ) = mi (y,ξ)) → (∀ y ξ, mo (y,-ξ) = mo (y,ξ)) →
      tsupport mi ⊆ closedBall 0 Rbase ×ˢ frequencyAnnulus a b →
      tsupport mo ⊆ closedBall 0 Rbase ×ˢ frequencyAnnulus a b →
      (∀ j z, ‖iteratedFDeriv ℝ j mi z‖ ≤ Hmask j) →
      (∀ j z, ‖iteratedFDeriv ℝ j mo z‖ ≤ Hmask j) →
      (∀ z ∈ tsupport mi, closedBall z buffer ⊆ interior {z | mo z = 1}) →
      ∀ Mi Mo : (SpacetimeL2 d (d+1)) →L[ℂ] (SpacetimeL2 d (d+1)),
        (∀ u : SpacetimeL2 d (d+1), Mi u =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (rightLocalizer ρ mi (fun z ↦ (u z).ofLp) y)) →
        (∀ u : SpacetimeL2 d (d+1), (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
          fun y ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun z ↦ (u z).ofLp) y)) →
      ∀ (W₁ : f.centers → TwoTimeAmplitude d (d+1))
        (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
        (T : f.centers → (SpacetimeL2 d (d+1)) →L[ℂ] (SpacetimeL2 d (d+1)))
        (reflected : Bool) (N : ℕ) (U : Set (Euclidean (d+1))) (hU : MeasurableSet U),
        tsupport μ ⊆ U → tsupport ν ⊆ U →
        let P := measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
          (selectedFullPhysicalResidualTerm f hK threshold Q B W₁ output
            houtput.continuous hob hib T (Sum.inr (), reflected))
        let Pdir := if backward then P.adjoint else P
        ∀ u : LocalL2 U (EuclideanSpace ℂ (Fin (d+1))),
          (1 - localRetardedOperator hU U Mo)
            (localRetardedOperator hU U Pdir (localRetardedOperator hU U Mi u)) ∈
            (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU).level m ∧
          (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU).gradeNorm m
            ((1 - localRetardedOperator hU U Mo)
              (localRetardedOperator hU U Pdir (localRetardedOperator hU U Mi u))) ≤
              Cmq N * ρ ^ ((m : ℝ) + (3*(d+1) : ℕ)) *
                L ^ bLoss * (L/ρ)^N * ‖u‖ := by
  classical
  let Kb := tsupport (fun y ↦ (output y : ℂ)) ×ˢ tsupport (fun y ↦ (f.inputMask y : ℂ))
  let Y := closedBall (0 : Euclidean (d+1)) Rbase
  have hKb : IsCompact Kb := (hoc.comp_left Complex.ofReal_zero).prod
    (f.inputMask_compact.comp_left Complex.ofReal_zero)
  have hY : IsCompact Y := isCompact_closedBall _ _
  obtain ⟨R, hR, hbound⟩ :=
    (isCompact_leakageOutputCarrier backward hKb hY).isBounded.exists_pos_norm_le
  let ψ : ContDiffBump (0 : Euclidean (d+1)) := ⟨R, R+1, hR, by linarith⟩
  have hplateau : ∀ y ∈ leakageOutputCarrier backward Kb Y, ψ y = 1 := by
    intro y hy
    exact ψ.one_of_mem_closedBall (by
      simpa only [mem_closedBall, dist_zero_right] using hbound y hy)
  obtain ⟨bLoss, Cmq, hCmq, hleak⟩ :=
    exists_local_measured_selectedFullPhysicalResidualTerm_elliptic_restriction_bound_of_uniform_masks
      f hK hΩ hball output houtput hoc hos hob threshold ht μ ν hμ hν hμc hνc hμb hνb
      AQ AB hAQ hAB e eu ez backward m ha J hJ ψ ψ.contDiff ψ.hasCompactSupport
      Y hY Hmask hHmask hbuffer hplateau
  refine ⟨bLoss, Cmq, hCmq, ?_⟩
  intro Rstar hRstar ρ L hL hLρ Q B hQ hB hmap hQl hBl hQp hBp
    mi mo Ki Oi Ko Oo hi ho hei heo hisupp hosupp hijets hojets hdiag
    Mi Mo hMi hMo W₁ hib T reflected N U hU hμs hνs P Pdir u
  have hbasei : Prod.fst '' tsupport mi ⊆ Y := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hisupp hp).1
  have hbaseo : Prod.fst '' tsupport mo ⊆ Y := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hosupp hp).1
  exact hleak mi mo hi.smooth hi.compactSupport hi.range ho hdiag hei heo
    (fun p hp ↦ (hisupp hp).2) hbasei hbaseo hijets hojets
    Rstar hRstar ρ L hL hLρ Mi Mo hMi hMo Q B hQ hB hmap hQl hBl hQp hBp
    W₁ hib T reflected N U hU hμs hνs u

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
