module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrescribedMeasuredRetardedLeakage
public import JanetCartan.Analysis.Microlocal.SelectedResidualInputs.ConicGraphs

/-!
# Prescribed leakage on the retained inverse's characteristic operators

Apply the actual conic-graph regularizations to the operator already retained by
`NormalizedBandInverse`, then use those regularizations in the prescribed-mask
leakage theorem. No new characteristic operator is selected. The proof preserves
both measurement masks and the literal adjoint.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 256
set_option maxRecDepth 4096
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly RegularSector.FinitePdo
open Characteristic Characteristic.ConicPhase Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open EvolutionLocalization EvolutionIntegratedLocalization FourierIntegral FiniteChain.Graph
open FiniteChain.Graph.PhysicalShells
universe uT uI uU uZ
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Z" => RootState (Euclidean d)

open SelectedEvenProofMasks ProtectedMasks JanetCartan.Localization
open Characteristic.ConicAmplitude Characteristic.ResidualCoordinates
open JanetCartan.CharacteristicTransport.CompleteResidual
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
open FiniteChain.Graph.PhysicalShells.Noncomparable
local notation "Mat" => MetricTensor (d+1)
local notation "V" => ℝ × JointVariables E

open FiniteChain.Graph.KernelLimits FourierIntegral.LowBounds FourierIntegral.LowBounds.FrequencyCutoff Pseudodifferential
open Characteristic.AmplitudeBounds Characteristic.UniformAmplitudes Characteristic.RootFamily
open Characteristic.EvolutionIntegral.KernelIdentification
open RegularSector.Characteristic.PdoRealization
local notation "Hspace" => SpacetimeL2 d (d+1)

/-- The original retained characteristic residual has the prescribed
measured leakage estimate, with constants before the current coefficients,
histories, proof masks and accuracy. The extra certificates are exactly the
phase, amplitude, endpoint-mask and `RetainedSignedRetardedBounds` outputs of
`exists_normalized_complete_smooth_fixed_inverse_of_selected_collar_on_enlarged_bands`.
The common-mask uniqueness continuation of
`exists_selected_common_conic_graph_regularizations` identifies its graph
integral with this supplied operator. No graph realization or leakage estimate
is assumed. Consumers: the same-inverse application of
`ObservedChains.measuredResidual_hchain_of_individual_estimates` and
`finiteChain_observation_rapidDecayAt.hleak`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_retained_prescribed_measured_retarded_leakage_constants
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hρb : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (ra rb : f.centers → ℝ) (hra : ∀ p, 0 < ra p) (hab : ∀ p, ra p ≤ rb p)
    (cost : f.centers → ℕ → ℝ) (hcost : ∀ p m, 0 < cost p m)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1) :
    ∀ a₀ b₀ : ℝ, 0 < a₀ →
      ∃ tlo thi : ℝ, 0 < tlo ∧ 0 < thi ∧
      ∀ (output : E → ℝ) (ho : ContDiff ℝ ∞ output), HasCompactSupport output →
      tsupport output ⊆ ball x f.physicalRadius →
      ∀ threshold : ℝ, f.radialThreshold ≤ threshold →
      ∀ {ι : Type uT} {κ : Type uI} {ιu : Type uU} {ιz : Type uZ} [Fintype ι] [Fintype κ] [Fintype ιu] [Fintype ιz],
      ∀ (eT : Module.Basis ι ℝ (JointVariables E))
        (eI : Module.Basis κ ℝ (ℝ × JointVariables E))
        (eu : OrthonormalBasis ιu ℝ E) (ez : OrthonormalBasis ιz ℝ E),
      ∀ J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E,
      MeasurePreserving (graphInputCoordinates J) volume volume →
      ∀ (buffer Rbase εcollar δT δI : ℝ) (Hmask Hcollar : ℕ → ℝ),
      (∀ j, 0 ≤ Hmask j) → (∀ j, 0 ≤ Hcollar j) →
      0 < εcollar → 0 < δT → 0 < δI →
      ∀ χ : V → ℂ, ContDiff ℝ ∞ χ →
      (∀ v, |v.1| ≤ εcollar / 4 → χ v = 1) →
      tsupport χ ⊆ {v | |v.1| ≤ εcollar / 2} →
      (∀ j v, ‖iteratedFDeriv ℝ j χ v‖ ≤ Hcollar j) →
      ∀ ψ : f.centers → E → ℝ, (∀ p, ContDiff ℝ ∞ (ψ p)) →
      (∀ p, HasCompactSupport (ψ p)) → (∀ p y, ‖ψ p y‖ ≤ 1) →
      (∀ p (backward : Bool) y, y ∈ (if backward then tsupport (chartInputMask f p)
        else tsupport (endpointOutputMask f p output)) → ψ p y = 1) →
      (∀ p y, y ∈ closedBall 0 Rbase → ψ p y = 1) →
      ∀ order : ℕ,
      ∃ (bLoss : f.centers → ℕ) (Cmq : f.centers → ℕ → ℝ),
      (∀ p q, 0 ≤ Cmq p q) ∧
      ∀ Rstar : ℕ, 10 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Fin (d+1) → Mat) (B : E → Mat),
      (∀ j, cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j-Rstar)) →
      (∀ j, cNorm (closedBall x RQ) j B ≤ A j * L ^ (j-Rstar)) →
      ∀ (Φ : f.centers → Z × ℝ → Z) (Cchart : f.centers → OpenPartialHomeomorph T T)
        (angular : f.centers → Euclidean d → ℝ),
      let h := fun p ↦ fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root
      let z := fun p ↦ ((coordinateSplit (f.chart p).index x).1,
        ((coordinateSplit (f.chart p).index x).2,
          (coordinateSplit (f.chart p).index p.val.val).2))
      let Fs := fun p ↦ selectedBufferedAmplitude f p Q B (Φ p) (Cchart p)
      let W := fun p (j : Fin 3) ↦
        collared (f.chart p).radialSection (if j=0 then 0 else 1) (angular p) (Fs p j)
      (∀ p, ContDiffOn ℝ ∞ (twoTimePhase (Cchart p)) (Cchart p).target) →
      (∀ p, closedBall ((z p).1, z p) (f.chart p).targetRadius ⊆ (Cchart p).target) →
      (∀ p, ∀ v ∈ (Cchart p).target, HasFDerivAt (twoTimePhase (Cchart p))
        (twoTimePhaseDifferential (h p) (Φ p) (Cchart p) v) v) →
      (∀ p, ∀ v ∈ closedBall ((z p).1, z p) (f.chart p).targetRadius,
        ‖twoTimePhaseMixed (Cchart p) v - 1‖ ≤ 1/2) →
      (∀ p j, cNorm (closedBall ((z p).1, z p) (f.chart p).targetRadius) j
        (twoTimePhase (Cchart p)) ≤ (f.chart p).phaseCost j *
          (1+cNorm (closedBall x RQ) (j+1) Q)) →
      (∀ p, ∀ η ∈ tsupport (angular p), 0 < (f.chart p).radialSection η) →
      (∀ p, ContDiff ℝ ∞ (angular p)) →
      (∀ p, ∀ ζ ∈ tsupport (fun ξ ↦ (dilatedConicMask (f.angularMask p) (2*threshold)
        (physicalCoordinates (f.chart p).index ξ) : ℂ)),
        conicMask (angular p) =ᶠ[𝓝 (spatialPart ζ)] fun _ ↦ (1 : ℝ)) →
      (∀ p j, ContDiff ℝ ∞ (Fs p j)) →
      (∀ p j, ContDiff ℝ ∞ (W p j)) →
      (∀ p, tsupport (Fs p 2) ⊆ closedBall ((z p).1, z p) ((f.chart p).bufferRadius/2)) →
      (∀ p j, tsupport (W p j) ⊆ ConicPhase.domain (f.chart p).radialSection
        ((Cchart p).target ∩ (Cchart p).symm ⁻¹'
          (ball (z p).1 ((f.chart p).maskRadius/2) ×ˢ
            (ball (z p).1 ((f.chart p).maskRadius/2) ×ˢ
              ball (z p).2 ((f.chart p).maskRadius/2))))) →
      (∀ p (v : T), (f.chart p).timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) →
        ∀ j : Fin (d+1), (fun k ↦ W p 2 v k j) =
          WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
            (fun y k ↦ W p 1
              (physicalSlice (coordinateSplit (f.chart p).index) v.2.1 v.2.2.2 y) k j)
            ((coordinateSplit (f.chart p).index).symm (v.1, v.2.2.1))) →
      (∀ p, ∀ v ∈ (Cchart p).target, ((Cchart p).symm v).2.1 = v.2.1) →
      (∀ p j m, BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1)
          (bufferedJetSet (f.chart p).radialSection (z p) ((f.chart p).bufferRadius/2)
            (ra p) (rb p)) m
          (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) j) ∧
        twoTimeOrderSeminorm (if j=0 then 0 else 1)
          (bufferedJetSet (f.chart p).radialSection (z p) ((f.chart p).bufferRadius/2)
            (ra p) (rb p)) m
          (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) j) ≤
          cost p m * (1+cNorm (closedBall x RQ) (m+10) Q+cNorm (closedBall x RQ) (m+9) B)) →
      ∀ (G : f.centers → T → ℝ) (χout χsource : f.centers → E → ℂ)
        (hs : ∀ p, ContDiff ℝ ∞ (χsource p))
        (base : f.centers → ℝ) (retainedCost : f.centers → ℕ → ℝ)
        (retained : f.centers → Hspace →L[ℂ] Hspace),
      (∀ p, ContDiff ℝ ∞ (G p)) →
      (∀ p, ∀ v ∈ tsupport (W p 0) ∪ tsupport (W p 1),
        G p =ᶠ[𝓝 v] ConicPhase.phase (f.chart p).radialSection (Cchart p)) →
      (∀ p (v : T), (f.chart p).timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) → W p 2 v ≠ 0 →
        G p =ᶠ[𝓝 v] ConicPhase.phase (f.chart p).radialSection (Cchart p)) →
      (∀ p, RetainedSignedRetardedBounds (closedBall x RQ) Q B
        (3*(f.chart p).maskRadius/4) ((z p).1-(f.chart p).maskRadius/2)
        (fun t s y η ↦ G p (t, (s, (y, η))))
        (twoTimePhysicalApply
          (fun y a ↦ (coefficient (f.chart p).index Q y a).map Complex.ofReal)
          (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal)
          (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) 1))
        (χout p) (χsource p) (selectedEndpointMultiplier f p threshold) (hs p)
        1 (base p) (retainedCost p) (retained p)) →
      ∀ (hob : ∀ y, ‖output y‖ ≤ 1) (hib : ∀ y, ‖f.inputMask y‖ ≤ 1),
      (∀ p y, (output y : ℂ) * χout p ((physicalCoordinates (f.chart p).index).symm y) =
        (output y : ℂ)) →
      (∀ p y, χsource p ((physicalCoordinates (f.chart p).index).symm y) *
        (f.inputMask y : ℂ) = (f.inputMask y : ℂ)) →
      ∀ Gext : f.centers → T → ℝ,
      (∀ p, ContDiffOn ℝ ∞ (Gext p) {q | q.2.2.2 ≠ 0}) →
      (∀ p, ∀ q ∈ ConicPhase.domain (f.chart p).radialSection
        (closedBall ((coordinateSplit (f.chart p).index x).1,
      ((coordinateSplit (f.chart p).index x).1,
        ((coordinateSplit (f.chart p).index x).2,
          (coordinateSplit (f.chart p).index p.val.val).2)))
      (2*(f.chart p).maskRadius)),
        (Gext p) =ᶠ[𝓝 q] ConicPhase.phase (f.chart p).radialSection (Cchart p)) →
      ∀ mif mof : f.centers → LocalizerSymbol (d+1),
      (∀ p, ContDiff ℝ ∞ (mif p)) → (∀ p, ContDiff ℝ ∞ (mof p)) →
      (∀ p, HasCompactSupport (mif p)) → (∀ p, HasCompactSupport (mof p)) →
      (∀ p z, mif p z ∈ Icc (0 : ℝ) 1) → (∀ p z, mof p z ∈ Icc (0 : ℝ) 1) →
      (∀ p, tsupport (mif p) ⊆ closedBall 0 Rbase ×ˢ frequencyAnnulus a₀ b₀) →
      (∀ p, tsupport (mof p) ⊆ closedBall 0 Rbase ×ˢ frequencyAnnulus a₀ b₀) →
      (∀ p j z, ‖iteratedFDeriv ℝ j (mif p) z‖ ≤ Hmask j) →
      (∀ p j z, ‖iteratedFDeriv ℝ j (mof p) z‖ ≤ Hmask j) →
      (∀ p, ∀ (o : Bool) (ρ : ℝ), 0 < ρ → ∀ (u y : E) (r' : ℝ) (w : JointVariables E),
        r' ∈ Icc 0 (6*f.physicalRadius) → r' ≤ (f.chart p).maskRadius →
        w.1.1 0 ∈ closedBall (coordinateSplit (f.chart p).index x).1 ((f.chart p).maskRadius/2) →
        spatialPart w.1.1 ∈ closedBall (coordinateSplit (f.chart p).index x).2 ((f.chart p).maskRadius/2) →
        spatialPart w.2.1 ∈ ConicPhase.radialSectionBand (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2 ((f.chart p).maskRadius/2) (ra p / thi) (ra p / tlo) →
        (y,w.2.2.1) ∈ cthickening (buffer/2) (tsupport (mif p)) →
        (u,w.2.2.2) ∈ tsupport (fun q ↦ 1-(mof p) q) →
        (δI ≤ phaseGradientSquare eI (jointElapsedPhase o
        (SymbolBudgets.normalizedTwoTimePhase ρ
          (curriedPhase (f.chart p).radialSection (Cchart p))) u y) (r',w) ∧
      (r' ≤ εcollar → δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase o
        (SymbolBudgets.normalizedTwoTimePhase ρ
          (curriedPhase (f.chart p).radialSection (Cchart p))) u y (r',w)) w)) ∧
        (δI ≤ phaseGradientSquare eI (jointElapsedPhase o
        (SymbolBudgets.normalizedTwoTimePhase ρ (fun t s u η ↦ (Gext p) (t,s,u,η))) u y) (r',w) ∧
      (r' ≤ εcollar → δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase o
        (SymbolBudgets.normalizedTwoTimePhase ρ (fun t s u η ↦ (Gext p) (t,s,u,η))) u y (r',w)) w))) →
      ∀ p : f.centers,
      let mi := mif p
      let mo := mof p
      let e := physicalCoordinates (f.chart p).index
      let Mout := sourceCutMultiplier (r := d+1) (output ∘ e)
        (ho.continuous.comp e.continuous) (fun y ↦ hob (e y))
      let Min := sourceCutMultiplier (r := d+1) (f.inputMask ∘ e)
        (f.inputMask_smooth.continuous.comp e.continuous) (fun y ↦ hib (e y))
      let Qop := Mout.comp ((retained p).comp Min)
      ∀ Mi Mo : Hspace →L[ℂ] Hspace,
        (∀ u : Hspace, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
          (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
        (∀ u : Hspace, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
          fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) →
      let Qm := measuredOperator
        (μ ∘ physicalCoordinates (f.chart p).index) (ν ∘ physicalCoordinates (f.chart p).index)
        (hμ.continuous.comp (physicalCoordinates (f.chart p).index).continuous)
        (hν.continuous.comp (physicalCoordinates (f.chart p).index).continuous)
        (fun y ↦ hμb _) (fun y ↦ hνb _) Qop
      ∀ accuracy (backward : Bool) u,
      MemVectorFourierSobolev (order : ℝ)
        ((1 - Mo) ((if backward then Qm.adjoint else Qm) (Mi u))) ∧
      vectorFourierSobolevNorm (order : ℝ)
        ((1 - Mo) ((if backward then Qm.adjoint else Qm) (Mi u))) ≤
        Cmq p accuracy * ρ ^ ((order : ℝ) + (3 * (d+1) : ℕ)) *
          L ^ bLoss p * (L / ρ) ^ accuracy * ‖u‖ := by
  classical
  obtain ⟨_, _, _, _, hleak⟩ :=
    exists_prescribed_measured_retarded_fourier_leakage_constants.{uT, uI, uU, uZ}
      f hρb hsrcρ ra rb hra hab cost hcost A hA μ ν hμ hν hμc hνc hμb hνb
  obtain ⟨θ, hθ⟩ := exists_selected_buffered_elapsed_cutoffs f hρb hsrcρ
  intro a₀ b₀ ha₀
  obtain ⟨tlo, thi, htlo, hthi, hleak⟩ := hleak a₀ b₀ ha₀
  refine ⟨tlo, thi, htlo, hthi, ?_⟩
  intro output ho hoc hout threshold ht
    ι κ ιu ιz _ _ _ _ eT eI eu ez J hJ
    buffer Rbase εcollar δT δI Hmask Hcollar hHmask hHcollar hε hδT hδI
    χ hχ hχone hχsupport hχder ψ hψ hψs hψb hψmask hψY order
  obtain ⟨bLoss, Cmq, hCmq, hleak⟩ := hleak output ho hoc hout threshold ht θ
    (fun p ↦ (hθ p).1) (fun p ↦ (hθ p).2.1) (fun p ↦ (hθ p).2.2.1)
    (fun p ↦ (hθ p).2.2.2) eT eI eu ez J hJ
    buffer Rbase εcollar δT δI Hmask Hcollar hHmask hHcollar hε hδT hδI
    χ hχ hχone hχsupport hχder ψ hψ hψs hψb hψmask hψY order
  refine ⟨bLoss, Cmq, hCmq, ?_⟩
  intro Rstar hRstar L ρ hL hρ Q B hQprofile hBprofile
    Φ Cchart angular h z Fs W hphase hbuffer hdiff hnear hphaseCost
    hangPos hang hplateau hFs hWs hFsSupport hsupport hphysical hsourceTime hseminorm
    G χout χsource hs base retainedCost retained hG hGgerm hGres hretained
    hob hib houtMask hsourceMask
    Gext hGext hGermExt mif mof hmi hmo hmic hmoc hmirange hmorange
    hmisupp hmosupp hmiJets hmoJets hshort
    p mi mo e Mout Min Qop Mi Mo hMi hMo Qm accuracy backward u
  obtain ⟨_, D, Treg, _, hbound, hreal, hrealAdj, hlim, hlimAdj,
    hm, Ocommon, _, hintegral, _, _, hsame⟩ :=
    SelectedResidualInputs.exists_selected_common_conic_graph_regularizations
      f p (hρb p) (hsrcρ p) threshold (f.radialThreshold_ge_one.trans ht)
      (angular p) (hang p) (hplateau p) output ho hoc hout Q B (h p) (Φ p) (Cchart p)
      (hbuffer p) (hphase p) (hdiff p) (hnear p) (hphaseCost p) (hsourceTime p)
      (Fs p) (hFs p) (hWs p) (hsupport p) (hphysical p)
      (G p) (hG p) (hGgerm p) (hGres p)
  have heq : Qop = Ocommon true :=
    (hsame true (χout p) (χsource p) (hs p) 1 (base p) (retainedCost p) (retained p)
      (hretained p) hob hib (houtMask p) (hsourceMask p)).1
  have hIntegral v : Qop v = elapsedGraphIntegral (3*(f.chart p).maskRadius/4)
      (curriedExtend (f.chart p).radialSection (twoTimePhase (Cchart p)))
      (directRetardedAmplitudes
        (fun y i ↦ (coefficient (f.chart p).index Q y i).map Complex.ofReal)
        (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal)
        (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) 0)
        (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) 1) true)
      (endpointOutputMask f p output) (chartInputMask f p)
      (selectedEndpointMultiplier f p threshold) v :=
    (congrArg (fun op : Hspace →L[ℂ] Hspace ↦ op v) heq).trans (hintegral true v)
  exact hleak Rstar hRstar L ρ hL hρ Q B hQprofile hBprofile
    Φ Cchart angular hphase hbuffer hdiff hnear hphaseCost hangPos hWs hFsSupport
    (fun p ↦ hsupport p 2) hphysical hsourceTime hseminorm
    Gext hGext hGermExt mif mof hmi hmo hmic hmoc hmirange hmorange
    hmisupp hmosupp hmiJets hmoJets hshort p
    (Treg true) (hreal true) (hrealAdj true)
    (fun j v ↦ (hm true j v).1) (fun j v ↦ (hm true j v).2)
    (hbound true) (hlim true) (hlimAdj true) Mi Mo Qop hMi hMo hIntegral
    accuracy backward u

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
