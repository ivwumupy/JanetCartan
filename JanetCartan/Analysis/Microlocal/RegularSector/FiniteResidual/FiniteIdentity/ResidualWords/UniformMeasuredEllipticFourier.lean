module

public import JanetCartan.Analysis.Microlocal.EllipticLocalization.CommonOutputDiagonal
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.MeasuredPdoCommon
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SignedLetterRestriction
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SupportedMaskProfiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.UniformDiagonal.Fourier

/-!
# Uniform measured elliptic leakage before varying proof masks

The actual elliptic symbol grades and normal-amplitude certificates supply
both measured graph regularizations. The common compact base, positive collar
and joint proof-mask profile determine the constants before varying masks,
coefficients and accuracy. Both physical measurements remain inside the amplitude.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 256
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.RegularSector.Realization
namespace JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
open FiniteMasks.ActualFamily EllipticComplement EllipticLocalization
open Characteristic.EvolutionIntegral Characteristic.PdoRealization
open Characteristic.RetardedLocalization Realization FiniteAssembly
open ArbitraryAccuracy.ResidualLocalization ArbitraryAccuracy.EvolutionLocalization
open ArbitraryAccuracy.SelectedLocalization ArbitraryAccuracy.EvolutionIntegratedLocalization
open CharacteristicTransport.CompleteResidual FourierIntegral
open FullLowBounds LowBounds LowBounds.FrequencyCutoff
open FiniteChain.Graph KernelLimits KernelEstimates
open PhysicalShells PhysicalShells.Comparable PhysicalShells.Noncomparable
open KernelEstimates.NoncomparableGeometry
open Pseudodifferential ResponseTransfer LocalSobolev
variable {d : ℕ}
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : (Fin (d+1) → MetricTensor (d+1))} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- The actual measured elliptic residual has arbitrary-accuracy Fourier
leakage with constants chosen before the varying proof masks and coefficient
fields. Only the common compact base, positive collar and joint proof-mask
profile precede the constants; these are the outputs of the protected even
mask construction. Both physical measurement masks and literal adjoints are
retained (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_measuredEllipticResidualPDO_fourier_leakage_constants_of_uniform_masks
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (output : Euclidean (d+1) → ℝ) (houtput : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    (threshold : ℝ) (ht : f.radialThreshold ≤ threshold)
    (μ ν : Euclidean (d+1) → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k)
    {ι ιu ιz : Type*} [Fintype ι] [Fintype ιu] [Fintype ιz]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean (d+1))))
    (eu : OrthonormalBasis ιu ℝ (Euclidean (d+1)))
    (ez : OrthonormalBasis ιz ℝ (Euclidean (d+1)))
    (backward : Bool) (m : ℕ) {a b : ℝ} (ha : 0 < a)
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] (Euclidean (d+1)))
    (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)
    (ψ : Euclidean (d+1) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (Y : Set (Euclidean (d+1))) (hY : IsCompact Y)
    (Hmask : ℕ → ℝ) (hHmask : ∀ k, 0 ≤ Hmask k)
    {buffer : ℝ} (hbuffer : 0 < buffer)
    (hplateau : ∀ y ∈ leakageOutputCarrier backward
      (tsupport (fun y ↦ (output y : ℂ)) ×ˢ tsupport (fun y ↦ (f.inputMask y : ℂ))) Y, ψ y = 1) :
    (∃ (bLoss : ℕ) (Cmq : ℕ → ℝ), (∀ N, 0 ≤ Cmq N) ∧
      ∀ (mi mo : LocalizerSymbol (d+1)) {Ko Oo : Set (Euclidean (d+1) × Euclidean (d+1))},
        ContDiff ℝ ∞ mi → HasCompactSupport mi → (∀ p, mi p ∈ Icc (0 : ℝ) 1) →
        IsBufferedLocalizer mo Ko Oo →
        (∀ p ∈ tsupport mi, closedBall p buffer ⊆ interior {p | mo p = 1}) →
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
      let P := measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
        ((sourceCutMultiplier output houtput.continuous hob).comp
          (maskedPhysicalPDO (fun y ↦ (f.outputMask y : ℂ))
            (fun y ↦ (f.inputMask y : ℂ)) (ellipticResidualSymbol f hK threshold Q B)));
      let Pdir := if backward then P.adjoint else P;
      ∀ N (u : (SpacetimeL2 d (d+1))), MemVectorFourierSobolev (m : ℝ) ((1-Mo) (Pdir (Mi u))) ∧
        vectorFourierSobolevNorm (m : ℝ) ((1-Mo) (Pdir (Mi u))) ≤
          Cmq N * ρ ^ ((m : ℝ) + (3*(d+1) : ℕ)) * L ^ bLoss * (L/ρ)^N * ‖u‖) := by
  let χo := fun y ↦ (μ y : ℂ)*(output y : ℂ)
  let χs := fun y ↦ (ν y : ℂ)*(f.inputMask y : ℂ)
  have hbase : tsupport χo ×ˢ tsupport χs ⊆
      tsupport (fun y ↦ (output y : ℂ)) ×ˢ tsupport (fun y ↦ (f.inputMask y : ℂ)) :=
    Set.prod_mono tsupport_mul_subset_right tsupport_mul_subset_right
  have hplateau' : ∀ y ∈ leakageOutputCarrier backward
      (tsupport χo ×ˢ tsupport χs) Y, ψ y = 1 := by
    intro y hy
    apply hplateau y
    cases backward <;> exact (Set.union_subset_union (Set.image_mono hbase) Subset.rfl) hy
  obtain ⟨Dc, hDc, hcomp⟩ := exists_elliptic_masked_comparable_profile f hK
    hΩ hball (fun y ↦ (output y : ℂ)) (Complex.ofRealCLM.contDiff.comp houtput)
    (hoc.comp_left Complex.ofReal_zero) (commonOutput_elliptic_carrier f output hoc hos).2
    threshold (f.radialThreshold_ge_one.trans ht) (b := b) ha AQ AB hAQ hAB
  obtain ⟨Dp, hDp, hphys⟩ := exists_elliptic_masked_noncomparable_profile f hK
    hΩ hball (fun y ↦ (output y : ℂ)) (Complex.ofRealCLM.contDiff.comp houtput)
    (hoc.comp_left Complex.ofReal_zero) (commonOutput_elliptic_carrier f output hoc hos).2
    AQ AB hAQ hAB
  let D : AmplitudeProfiles := {
    symbol := fun k ↦ Dc k + Dp k
    graphCutoff := fun _ ↦ 0
    outputCutoff := fun _ ↦ 0
    inputMask := Hmask
    outputMask := Hmask
    symbol_nonneg := fun k ↦ add_nonneg (hDc k) (hDp k)
    graphCutoff_nonneg := fun _ ↦ le_rfl
    outputCutoff_nonneg := fun _ ↦ le_rfl
    inputMask_nonneg := hHmask
    outputMask_nonneg := hHmask
    symbolOffset := 0
    graphCutoffOffset := 0
    outputCutoffOffset := 0
    inputMaskOffset := 0
    outputMaskOffset := 0 }
  obtain ⟨Dm, _, hinProf, houtProf, hio, hoo, _, hmeasure⟩ :=
    exists_measured_maskedPDO_symbol_profiles (q := d+1) μ ν hμ hν hμc hνc D
  obtain ⟨bLoss, Cmq, hCmq, hbound⟩ :=
    UniformDiagonal.exists_directPDO_fourier_bound_of_uniform_masks e eu ez backward (-1) m ha
    χo χs (hoc.comp_left Complex.ofReal_zero).mul_left
    (f.inputMask_compact.comp_left Complex.ofReal_zero).mul_left
    J hJ ψ hψ hsψ Y Y hY hY hplateau' Dm Hmask hHmask hbuffer
  refine ⟨bLoss, Cmq, hCmq, ?_⟩
  intro mi mo Ko Oo hi his hirange ho hdiag hiAnn hbasei hbaseo hmi hmo
    Rstar hR ρ L hL hLρ Mi Mo hMi hMo Q B hQ hB hmap hQl hBl hQp hBp P Pdir N u
  let c := ellipticResidualSymbol f hK threshold Q B
  have hc : c ∈ ({ellipticInverseSymbol f hK threshold Q,
      ellipticResidualSymbol f hK threshold Q B, ellipticSourceSymbol f hK threshold} :
      Set (Euclidean (d+1) → Euclidean (d+1) → (Matrix (Fin (d+1)) (Fin (d+1)) ℂ))) := by simp [c]
  obtain ⟨R, _, C, _, _, _, hbudget⟩ := exists_ellipticSymbols_pdo_budgets f hK hΩ hball
  have hn := (hbudget threshold ht Q B hQ hB hmap hQl hBl c (Or.inr rfl)).1
  have houtputPlateau := commonOutput_mul_elliptic_outputMask f output hos
  obtain ⟨hsm, Preg, _, hreal, hlim⟩ := exists_measured_commonOutputPDO_oriented_regularizations
    (fun y ↦ (f.outputMask y : ℂ)) (fun y ↦ (f.inputMask y : ℂ)) c (f.outputMask_compact.comp_left Complex.ofReal_zero)
    (f.inputMask_compact.comp_left Complex.ofReal_zero) hn output houtput hob houtputPlateau
    μ ν hμ hν hμb hνb
  have hraw := (exists_commonOutput_ellipticPDO_oriented_regularizations f hK
    hΩ hball output houtput hoc hos hob ht Q B hQ hB hmap hQl hBl c hc).1
  have hcgrade := hcomp Rstar hR L ρ hL (hL.trans hLρ) Q B hQ hB hmap
    hQp hBp true backward
  have hpgrade := hphys Rstar hR L ρ hL (zero_lt_one.trans_le (hL.trans hLρ))
    threshold ht Q B hQ hB hmap
    ((cNorm_mono_order (by omega : 1 ≤ 2*(d+2)+2)).trans hQl)
    ((cNorm_mono_order (Nat.zero_le _)).trans hBl) hQp hBp c (Or.inr rfl) backward
  have henlarge (r : ℝ) (hr : 0 ≤ r) (k : ℕ) {a₁ : ℝ} (ha₁ : a₁ ≤ D.symbol k) :
      r ^ (-1 : ℝ) * a₁ * L ^ k ≤ r ^ (-1 : ℝ) * D.symbol k * L ^ (k+D.symbolOffset) := by
    dsimp only [D, Nat.add_zero] at ha₁ ⊢
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ha₁ (Real.rpow_nonneg hr _))
      (pow_nonneg (zero_le_one.trans hL) _)
  have hmeasured := hmeasure (LinearIsometryEquiv.refl ℝ (Euclidean (d+1)))
    (fun y ↦ (output y : ℂ)) (fun y ↦ (f.inputMask y : ℂ)) c backward
    (hraw backward) ρ L (-1) hL _ _
    (fun k v hv ↦ (hcgrade k v hv).trans
      (henlarge ρ (zero_le_one.trans (hL.trans hLρ)) k
        (le_add_of_nonneg_right (hDp k))))
    (fun low j ξ hξ z hz k ↦ (hpgrade low j ξ hξ z hz k).trans
      (henlarge _ (zero_le_one.trans (le_max_left _ _)) k
        (le_add_of_nonneg_left (hDc k))))
  have hin := (selected_localizer_slices_le_joint_profile mi hi Hmask hHmask hmi hL).1
  have hout := (selected_localizer_slices_le_joint_profile mo ho.smooth Hmask hHmask hmo hL).2.2.2
  have hcarrier : comparableJointCarrier 1 1 a b
      ((Prod.fst '' (tsupport χo ×ˢ tsupport χs)) ×ˢ frequencyAnnulus
        (a / (16*annulusFactor 1 1)) (4*max 1 (4*annulusFactor 1 1*b)))
      (tsupport χo ×ˢ tsupport χs) (frequencyAnnulus a b) ⊆
    comparableJointCarrier 1 1 a b
      ((Prod.fst '' (tsupport (fun y ↦ (output y : ℂ)) ×ˢ tsupport (fun y ↦ (f.inputMask y : ℂ)))) ×ˢ frequencyAnnulus
        (a / (16*annulusFactor 1 1)) (4*max 1 (4*annulusFactor 1 1*b)))
      (tsupport (fun y ↦ (output y : ℂ)) ×ˢ tsupport (fun y ↦ (f.inputMask y : ℂ))) (frequencyAnnulus a b) := by
    intro v hv
    exact ⟨⟨hbase hv.1.1, hv.1.2⟩, ⟨Set.image_mono hbase hv.2.1, hv.2.2⟩⟩
  obtain ⟨Mi', Mo', hMi', hMo', hleak⟩ := hbound mi mo hi his hirange ho hdiag
    hiAnn hbasei hbaseo hmo ρ L hL hLρ
  have hei : Mi' = Mi := eq_of_rightLocalizer_representatives ρ mi Mi' Mi hMi' hMi
  have heo : Mo' = Mo := eq_of_leftLocalizer_representatives ρ mo Mo' Mo hMo' hMo
  subst Mi'
  subst Mo'
  have hcall := hleak (0 : Euclidean (d+1) → Fin (d+1) → (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) (0 : Euclidean (d+1) → (Matrix (Fin (d+1)) (Fin (d+1)) ℂ))
    (0 : TwoTimeAmplitude d (d+1)) c (fun _ _ ↦ 1) (fun _ ↦ 1) 0
  have hec : directPDOSymbols (0 : Euclidean (d+1) → Fin (d+1) → (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) (0 : Euclidean (d+1) → (Matrix (Fin (d+1)) (Fin (d+1)) ℂ))
      (0 : TwoTimeAmplitude d (d+1)) c (fun _ _ ↦ 1) (fun _ ↦ 1) 0 = c := by
    funext y ξ
    simp [directPDOSymbols, directAlgebraicSymbol]
  rw [hec] at hcall
  have hfreq := elliptic_masked_amplitude_support f hK (fun y ↦ (output y : ℂ))
    (zero_lt_one.trans_le (f.radialThreshold_ge_one.trans ht)) Q B
  have hzero (y z ξ : Euclidean (d+1)) (hξ : ξ ∉ tsupport (ellipticSourceMask f hK threshold)) :
      orientedMaskedPDOAmplitude backward χo χs c y z ξ = 0 := by
    have he := measured_orientedPDOAmplitude_eq μ ν (LinearIsometryEquiv.refl ℝ (Euclidean (d+1)))
      (fun y ↦ (output y : ℂ)) (fun y ↦ (f.inputMask y : ℂ)) c backward y z ξ
    rw [hfreq.2.2.2 c hc backward y z ξ (Or.inr hξ), smul_zero] at he
    exact he
  have hp := hcall (hsm backward)
    (fun k v hv ↦ hmeasured.1 k v (hcarrier hv))
    (fun y _ k v _ ↦ by simpa only [hinProf, hio, D, Nat.add_zero] using hin k y v)
    (fun low j ξ hξ z hz k ↦ hmeasured.2 low j ξ hξ z (hbase hz) k)
    (by simpa only [houtProf, hoo, D, Nat.add_zero] using fun y ξ k ↦ hout k y ξ)
    (tsupport (ellipticSourceMask f hK threshold)) hfreq.1 hfreq.2.1 hzero
    complexPhysicalCutoff (fun _ _ _ ↦ rfl) (Preg backward) (hreal backward) (hlim backward) N u
  have hP : P = maskedPhysicalPDO χo χs c := by
    dsimp only [P]
    rw [commonOutput_ellipticPDO_eq_masked f hK hΩ hball output houtput hos hob
      ht Q B hQ hB hmap hQl hBl c hc]
    exact measured_commonOutputPDO_eq (fun y ↦ (f.outputMask y : ℂ)) (fun y ↦ (f.inputMask y : ℂ)) c hn output houtput hob houtputPlateau
      μ ν hμ hν hμb hνb
  dsimp only [Pdir]
  rw [hP]
  simpa only [show max (0 : ℝ) (-1) = 0 by norm_num, zero_add] using hp

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
