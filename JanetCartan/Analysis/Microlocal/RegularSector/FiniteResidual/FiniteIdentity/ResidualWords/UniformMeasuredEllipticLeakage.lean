module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords.UniformMeasuredEllipticFourier
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Physical

/-!
# Measured signed elliptic leakage

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
namespace JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
open FiniteMasks.ActualFamily EllipticComplement Characteristic.EvolutionIntegral
open Characteristic.RetardedLocalization Realization
open ArbitraryAccuracy.ResidualLocalization ArbitraryAccuracy.EvolutionLocalization
open CharacteristicTransport.CompleteResidual FourierIntegral
open FullLowBounds LowBounds LowBounds.FrequencyCutoff
open FiniteChain.Graph KernelLimits KernelEstimates
open PhysicalShells PhysicalShells.Comparable PhysicalShells.Noncomparable
open KernelEstimates.NoncomparableGeometry
open Pseudodifferential ResponseTransfer LocalSobolev FiniteAssembly
open ArbitraryAccuracy.SelectedLocalization
variable {d : ℕ}
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- Apply the actual uniform measured Fourier estimate to each normalized elliptic
letter, with its external half and physical `1/i`. The constants precede the
varying proof masks and coefficient fields. All coefficient fields,
mask positions, reflections and adjoint orientations are retained. This is
the elliptic-letter input for the actual measured ordered-word consumer
`NormalizedResidualWords.measured_realResidual_hchain_of_words`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_measured_selectedFullPhysicalResidualTerm_elliptic_restriction_bound_of_uniform_masks
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
    (ψ : Euclidean (d+1) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (Y : Set (Euclidean (d+1))) (hY : IsCompact Y)
    (Hmask : ℕ → ℝ) (hHmask : ∀ k, 0 ≤ Hmask k)
    {buffer : ℝ} (hbuffer : 0 < buffer)
    (hplateau : ∀ y ∈ leakageOutputCarrier backward
      (tsupport (fun y ↦ (output y : ℂ)) ×ˢ tsupport (fun y ↦ (f.inputMask y : ℂ))) Y, ψ y = 1) :
    ∃ (bLoss : ℕ) (Cmq : ℕ → ℝ),
      (∀ N, 0 ≤ Cmq N) ∧
      ∀ (mi mo : LocalizerSymbol (d+1)) {Ko Oo : Set (Euclidean (d+1) × Euclidean (d+1))},
        ContDiff ℝ ∞ mi → HasCompactSupport mi → (∀ p, mi p ∈ Icc (0 : ℝ) 1) →
        IsBufferedLocalizer mo Ko Oo →
        (∀ p ∈ tsupport mi, closedBall p buffer ⊆ interior {p | mo p = 1}) →
        (∀ y ξ, mi (y, -ξ) = mi (y, ξ)) →
        (∀ y ξ, mo (y, -ξ) = mo (y, ξ)) →
        (∀ p ∈ tsupport mi, p.2 ∈ frequencyAnnulus a b) →
        Prod.fst '' tsupport mi ⊆ Y → Prod.fst '' tsupport mo ⊆ Y →
        (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Hmask k) →
        (∀ k p, ‖iteratedFDeriv ℝ k mo p‖ ≤ Hmask k) →
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ ρ L : ℝ, 1 ≤ L → L ≤ ρ →
      ∀ Mi Mo : (SpacetimeL2 d (d+1)) →L[ℂ] (SpacetimeL2 d (d+1)),
        (∀ u : (SpacetimeL2 d (d+1)), Mi u =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (rightLocalizer ρ mi (fun z ↦ (u z).ofLp) y)) →
        (∀ u : (SpacetimeL2 d (d+1)), (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
          fun y ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun z ↦ (u z).ofLp) y)) →
      ∀ (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
        (B : Euclidean (d+1) → MetricTensor (d+1)),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M →
        cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ (W₁ : f.centers → TwoTimeAmplitude d (d+1))
        (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
        (T : f.centers → (SpacetimeL2 d (d+1)) →L[ℂ] (SpacetimeL2 d (d+1)))
        (reflected : Bool) (N : ℕ) (U : Set (Euclidean (d+1))) (hU : MeasurableSet U),
        let P := measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
          (selectedFullPhysicalResidualTerm f hK threshold Q B W₁ output
            houtput.continuous hob hib T (Sum.inr (), reflected))
        let Pdir := if backward then P.adjoint else P
        (∀ u : (SpacetimeL2 d (d+1)),
          restrictL2 U ((1 - Mo) (Pdir (Mi u))) ∈
            (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU).level m ∧
          (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU).gradeNorm m
            (restrictL2 U ((1 - Mo) (Pdir (Mi u)))) ≤
              Cmq N * ρ ^ ((m : ℝ) + (3*(d+1) : ℕ)) *
                L ^ bLoss * (L/ρ)^N * ‖u‖) := by
  obtain ⟨bLoss, Cmq, hCmq, hb⟩ :=
    exists_measuredEllipticResidualPDO_fourier_leakage_constants_of_uniform_masks f hK hΩ hball
      output houtput hoc hos hob threshold ht μ ν hμ hν hμc hνc hμb hνb
      AQ AB hAQ hAB e eu ez backward m ha
      J hJ ψ hψ hsψ Y hY Hmask hHmask hbuffer hplateau
  obtain ⟨C, hC, hcompare⟩ := exists_signedLetter_fourier_restriction_comparison d (d+1) m
  let z : ℂ := (1/2) * (1/Complex.I)
  refine ⟨bLoss, fun N ↦ C * Cmq N * ‖z‖,
    fun N ↦ mul_nonneg (mul_nonneg hC.le (hCmq N)) (norm_nonneg z), ?_⟩
  intro mi mo Ko Oo hi his hirange ho hdiag hieven hoeven hiAnn hbasei hbaseo hmi hmo
    Rstar hR ρ L hL hLρ Mi Mo hMi hMo Q B hQ hB hmap hQl hBl hQp hBp
    W₁ hib T reflected N U hU P Pdir u
  let A := measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
    ((sourceCutMultiplier output houtput.continuous hob).comp
      (maskedPhysicalPDO (fun y ↦ (f.outputMask y : ℂ))
        (fun y ↦ (f.inputMask y : ℂ)) (ellipticResidualSymbol f hK threshold Q B)))
  have hscalar : measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      ((1/2 : ℂ) • ((sourceCutMultiplier output houtput.continuous hob).comp
        (ellipticResidual f hK threshold Q B))) = z • A := by
    simp only [A, z, ellipticResidual, measuredOperator,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, smul_smul]
  have hP : P = if reflected then boundedConjugate (z • A) else z • A := by
    dsimp only [P, selectedFullPhysicalResidualTerm, Sum.elim_inr]
    cases reflected with
    | false => exact hscalar
    | true =>
      simp only [ite_true, ← boundedConjugate_measuredOperator, hscalar]
  have hρ : ρ ≠ 0 := (zero_lt_one.trans_le (hL.trans hLρ)).ne'
  have histar := boundedRightLocalizer_star_of_even ρ mi hieven Mi hMi
  have hostar := boundedLeftLocalizer_star_of_even hρ mo ho.smooth.continuous
    ho.compactSupport hoeven Mo hMo
  let cost := Cmq N * ρ ^ ((m : ℝ) + (3*(d+1) : ℕ)) * L ^ bLoss * (L/ρ)^N
  have hcost : 0 ≤ cost := by
    dsimp [cost]
    exact mul_nonneg (mul_nonneg (mul_nonneg (hCmq N)
      (Real.rpow_nonneg (zero_le_one.trans (hL.trans hLρ)) _))
      (pow_nonneg (zero_le_one.trans hL) _))
      (pow_nonneg (div_nonneg (zero_le_one.trans hL)
        (zero_le_one.trans (hL.trans hLρ))) _)
  have hbound := hcompare U hU A Mi Mo histar hostar z reflected backward cost hcost
    (fun v ↦ hb mi mo hi his hirange ho hdiag hiAnn hbasei hbaseo hmi hmo Rstar hR ρ L hL hLρ Mi Mo hMi hMo Q B hQ hB hmap hQl hBl hQp hBp N v) u
  dsimp only [Pdir]
  rw [hP]
  simpa only [cost, mul_assoc, mul_left_comm, mul_comm] using hbound


/-- Uniformly over the supplied proof-mask profile, the original measured
normalized elliptic letter satisfies the local leakage bound on the inverse space. Both intermediate zero extensions are
identified using the actual physical mask supports, also in the literal
adjoint orientation. This is the elliptic factor of
`NormalizedResidualWords.measured_realResidual_hchain_of_words`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_local_measured_selectedFullPhysicalResidualTerm_elliptic_restriction_bound_of_uniform_masks
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
    (ψ : Euclidean (d+1) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (Y : Set (Euclidean (d+1))) (hY : IsCompact Y)
    (Hmask : ℕ → ℝ) (hHmask : ∀ k, 0 ≤ Hmask k)
    {buffer : ℝ} (hbuffer : 0 < buffer)
    (hplateau : ∀ y ∈ leakageOutputCarrier backward
      (tsupport (fun y ↦ (output y : ℂ)) ×ˢ tsupport (fun y ↦ (f.inputMask y : ℂ))) Y, ψ y = 1) :
    ∃ (bLoss : ℕ) (Cmq : ℕ → ℝ),
      (∀ N, 0 ≤ Cmq N) ∧
      ∀ (mi mo : LocalizerSymbol (d+1)) {Ko Oo : Set (Euclidean (d+1) × Euclidean (d+1))},
        ContDiff ℝ ∞ mi → HasCompactSupport mi → (∀ p, mi p ∈ Icc (0 : ℝ) 1) →
        IsBufferedLocalizer mo Ko Oo →
        (∀ p ∈ tsupport mi, closedBall p buffer ⊆ interior {p | mo p = 1}) →
        (∀ y ξ, mi (y, -ξ) = mi (y, ξ)) →
        (∀ y ξ, mo (y, -ξ) = mo (y, ξ)) →
        (∀ p ∈ tsupport mi, p.2 ∈ frequencyAnnulus a b) →
        Prod.fst '' tsupport mi ⊆ Y → Prod.fst '' tsupport mo ⊆ Y →
        (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Hmask k) →
        (∀ k p, ‖iteratedFDeriv ℝ k mo p‖ ≤ Hmask k) →
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ ρ L : ℝ, 1 ≤ L → L ≤ ρ →
      ∀ Mi Mo : (SpacetimeL2 d (d+1)) →L[ℂ] (SpacetimeL2 d (d+1)),
        (∀ u : (SpacetimeL2 d (d+1)), Mi u =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (rightLocalizer ρ mi (fun z ↦ (u z).ofLp) y)) →
        (∀ u : (SpacetimeL2 d (d+1)), (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
          fun y ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun z ↦ (u z).ofLp) y)) →
      ∀ (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
        (B : Euclidean (d+1) → MetricTensor (d+1)),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M →
        cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ (W₁ : f.centers → TwoTimeAmplitude d (d+1))
        (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
        (T : f.centers → (SpacetimeL2 d (d+1)) →L[ℂ] (SpacetimeL2 d (d+1)))
        (reflected : Bool) (N : ℕ) (U : Set (Euclidean (d+1))) (hU : MeasurableSet U),
        tsupport μ ⊆ U → tsupport ν ⊆ U →
        let P := measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
          (selectedFullPhysicalResidualTerm f hK threshold Q B W₁ output
            houtput.continuous hob hib T (Sum.inr (), reflected))
        let Pdir := if backward then P.adjoint else P
        (∀ u : LocalL2 U (EuclideanSpace ℂ (Fin (d+1))),
          (1 - localRetardedOperator hU U Mo)
            (localRetardedOperator hU U Pdir (localRetardedOperator hU U Mi u)) ∈
            (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU).level m ∧
          (restrictionSobolevScale U (EuclideanSpace ℂ (Fin (d+1))) hU).gradeNorm m
            ((1 - localRetardedOperator hU U Mo)
              (localRetardedOperator hU U Pdir (localRetardedOperator hU U Mi u))) ≤
              Cmq N * ρ ^ ((m : ℝ) + (3*(d+1) : ℕ)) *
                L ^ bLoss * (L/ρ)^N * ‖u‖) := by
  obtain ⟨bLoss, Cmq, hCmq, hb⟩ :=
    exists_measured_selectedFullPhysicalResidualTerm_elliptic_restriction_bound_of_uniform_masks f hK
      hΩ hball output houtput hoc hos hob threshold ht μ ν hμ hν hμc hνc hμb hνb
      AQ AB hAQ hAB e eu ez backward m ha
      J hJ ψ hψ hsψ Y hY Hmask hHmask hbuffer hplateau
  refine ⟨bLoss, Cmq, hCmq, ?_⟩
  intro mi mo Ko Oo hi his hirange ho hdiag hieven hoeven hiAnn hbasei hbaseo hmi hmo
    Rstar hR ρ L hL hLρ Mi Mo hMi hMo Q B hQ hB hmap hQl hBl hQp hBp
    W₁ hib T reflected N U hU hμs hνs P Pdir u
  have hleak := hb mi mo hi his hirange ho hdiag hieven hoeven hiAnn hbasei hbaseo hmi hmo
    Rstar hR ρ L hL hLρ Mi Mo hMi hMo Q B hQ hB hmap hQl hBl
    hQp hBp W₁ hib T reflected N U hU (SmallSupport.zeroExtend hU u)
  have he := selectedFullPhysicalResidualTerm_local_leakage_eq f hK threshold Q B W₁
    output houtput.continuous hob hib T (Sum.inr (), reflected)
    μ ν hμ.continuous hν.continuous hμb hνb hU hμs hνs Mi Mo backward u
  change _ = restrictL2 U ((1-Mo) (Pdir (Mi (SmallSupport.zeroExtend hU u)))) at he
  rw [he]
  simpa only [LinearIsometry.norm_map] using hleak

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
