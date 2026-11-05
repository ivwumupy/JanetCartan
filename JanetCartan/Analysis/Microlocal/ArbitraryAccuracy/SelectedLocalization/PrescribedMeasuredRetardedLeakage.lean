module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.ActualRetardedLeakage
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrescribedSupportedPhaseApplication
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.MeasuredElapsedInputs
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.MeasuredSupportedGraphs

/-!
# Measured retarded leakage for prescribed terminal masks

The original phase, amplitude and even-mask producers supply every primitive
input. Measurement covariance identifies the original retarded operator and its
literal adjoint with their common masked graph limits.
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
variable {d q : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
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

/-- Apply the actual phase, measured amplitude and common graph-limit
producers with the prescribed proof masks and primitive geometric gaps.
Both physical measurement masks and the full zeroth coefficient remain in the
literal operator. All leakage constants precede the varying coefficients,
proof masks and accuracy. The same masks may retain a terminal plateau from
`NormalizedTerminalProtection.exists_original_history_terminal_even_proof_masks`.
Consumer: `finiteChain_observation_rapidDecayAt.hleak` for the characteristic
retarded letters (`app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:energy-complete-residual`,
`app:ch_regular_base:eq:measured-adjoint`). -/
theorem exists_prescribed_measured_retarded_fourier_leakage_constants
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hρb : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (ra rb : f.centers → ℝ) (hra : ∀ p, 0 < ra p) (hab : ∀ p, ra p ≤ rb p)
    (cost : f.centers → ℕ → ℝ) (hcost : ∀ p m, 0 < cost p m)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ a₀ b₀ : ℝ, 0 < a₀ →
      ∃ tlo thi : ℝ, 0 < tlo ∧ 0 < thi ∧
      ∀ output : E → ℝ, ContDiff ℝ ∞ output → HasCompactSupport output →
      tsupport output ⊆ ball x f.physicalRadius →
      ∀ threshold : ℝ, f.radialThreshold ≤ threshold →
      ∀ θ : f.centers → ℝ → ℂ, (∀ p, ContDiff ℝ ∞ (θ p)) →
      (∀ p, HasCompactSupport (θ p)) →
      (∀ p r, r ∈ Icc 0 (3*(f.chart p).maskRadius/4) → θ p r = 1) →
      (∀ p, tsupport (θ p) ⊆ ball 0
        (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius)) →
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
      (∀ p j, ContDiff ℝ ∞ (W p j)) →
      (∀ p, tsupport (Fs p 2) ⊆ closedBall ((z p).1, z p) ((f.chart p).bufferRadius/2)) →
      (∀ p, tsupport (W p 2) ⊆ ConicPhase.domain (f.chart p).radialSection
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
      let Δ := 3*(f.chart p).maskRadius/4
      let χout := endpointOutputMask f p output
      let χsource := chartInputMask f p
      let β := selectedEndpointMultiplier f p threshold
      let Ψoriginal := curriedExtend (f.chart p).radialSection (twoTimePhase (Cchart p))
      let Aoriginal := fun y i ↦ (coefficient (f.chart p).index Q y i).map Complex.ofReal
      let Boriginal := fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal
      let W₀original := selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) 0
      let W₁original := selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) 1
    ∀ (Treg : ℕ → ℝ → Hspace →L[ℂ] Hspace)
    (hreal : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) (d+1),
      Treg j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψoriginal r)
        (frequencyCutFullAmplitude (complexPhysicalCutoff j) (elapsedAmplitude (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original true) χout χsource β r)) u)
    (hrealAdj : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) (d+1),
      (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψoriginal r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
            (fun x z ξ ↦ (elapsedAmplitude (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original true) χout χsource β r x z ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) z))
    (hm : ∀ j u, AEStronglyMeasurable (fun r ↦ Treg j r u) (volume.restrict (Icc 0 Δ)))
    (hmAdj : ∀ j u, AEStronglyMeasurable (fun r ↦ (Treg j r).adjoint u)
      (volume.restrict (Icc 0 Δ)))
    {LOW : ℝ} (hbound : ∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ LOW)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop
      (𝓝 (elapsedGraph Ψoriginal (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original true) χout χsource β r u)))
    (hlimAdj : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Treg j r).adjoint u) atTop
      (𝓝 ((elapsedGraph Ψoriginal (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original true) χout χsource β r).adjoint u))),
    ∀ Mi Mo Qop : Hspace →L[ℂ] Hspace,
      (∀ u : Hspace, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      (∀ u : Hspace, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) →
      (∀ u, Qop u = elapsedGraphIntegral Δ Ψoriginal
        (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original true)
        χout χsource β u) →
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
  have phaseInputs := exists_prescribed_supported_elapsed_phase_inputs.{uT, uI}
    (d := d) (q := d+1) (Ω := Ω) (x := x) (RQ := RQ) (A₀ := A₀) (K := K) (M := M)
    f hρb hsrcρ ra rb hra hab A hA
  rcases phaseInputs with ⟨c, phaseInputs⟩
  rcases phaseInputs with ⟨C, phaseInputs⟩
  rcases phaseInputs with ⟨hc, phaseInputs⟩
  rcases phaseInputs with ⟨hC, hphase⟩
  refine Exists.intro c ?_
  refine Exists.intro C ?_
  refine And.intro hc ?_
  refine And.intro hC ?_
  intro a₀ b₀ ha₀
  have timeInputs := hphase a₀ b₀ ha₀
  rcases timeInputs with ⟨tlo, timeInputs⟩
  rcases timeInputs with ⟨thi, timeInputs⟩
  rcases timeInputs with ⟨htlo, timeInputs⟩
  rcases timeInputs with ⟨hthi, hphase⟩
  refine ⟨tlo, thi, htlo, hthi, ?_⟩
  intro output ho hoc hout threshold ht θ hθ hθs hθone hθbuffer
    ι κ ιu ιz _ _ _ _ eT eI eu ez J hJ
    buffer Rbase εcollar δT δI Hmask Hcollar hHmask hHcollar hε hδT hδI
    χ hχ hχone hχsupport hχder ψ hψ hψs hψb hψmask hψY order
  let Kg := fun p ↦ selectedResidualComparableCarrier f p output threshold c C a₀ b₀
  let Kjet := fun p ↦ selectedRetainedResidualCarrier f p output threshold c C a₀ b₀
    (θ p) (ra p) (rb p) tlo thi
  have phaseData := hphase output ho hoc hout threshold ht θ hθs hθbuffer
  rcases phaseData with ⟨hKg, phaseData⟩
  rcases phaseData with ⟨hKjet, phaseData⟩
  rcases phaseData with ⟨hsub, phaseData⟩
  rcases phaseData with ⟨hsupport, phaseData⟩
  rcases phaseData with ⟨P₀, phaseData⟩
  rcases phaseData with ⟨Pbase, phaseData⟩
  rcases phaseData with ⟨hP₀, phaseData⟩
  rcases phaseData with ⟨hPbase, phaseData⟩
  rcases phaseData with ⟨Vphase, phaseData⟩
  rcases phaseData with ⟨Ua, phaseData⟩
  rcases phaseData with ⟨Kphysical, phaseData⟩
  rcases phaseData with ⟨hVphase, phaseData⟩
  rcases phaseData with ⟨hUa, phaseData⟩
  rcases phaseData with ⟨hKphysical, phaseData⟩
  rcases phaseData with ⟨hKV, phaseData⟩
  rcases phaseData with ⟨hUabuffer, phaseData⟩
  rcases phaseData with ⟨hUapos, phaseData⟩
  rcases phaseData with ⟨hphysicalMap, phaseData⟩
  rcases phaseData with ⟨hcarrier, phaseData⟩
  have hphase := @phaseData
  have amplitudeData := exists_selected_measured_elapsed_amplitude_inputs_of_joint_localizer_profile f hρb hsrcρ
      c C a₀ b₀ ha₀ ra rb hra hab cost hcost A hA output ho hoc hout threshold ht
      (fun p ↦ 3*(f.chart p).maskRadius/4) θ hθs hθone μ ν hμ hν hμc hνc Hmask hHmask
  rcases amplitudeData with ⟨Kglobal, amplitudeData⟩
  rcases amplitudeData with ⟨Kelapsed, amplitudeData⟩
  rcases amplitudeData with ⟨Qt, amplitudeData⟩
  rcases amplitudeData with ⟨Qs, amplitudeData⟩
  rcases amplitudeData with ⟨Qg, amplitudeData⟩
  rcases amplitudeData with ⟨Qb, amplitudeData⟩
  rcases amplitudeData with ⟨Qi, amplitudeData⟩
  rcases amplitudeData with ⟨O, amplitudeData⟩
  rcases amplitudeData with ⟨Wave, amplitudeData⟩
  rcases amplitudeData with ⟨Bbase, amplitudeData⟩
  rcases amplitudeData with ⟨D, amplitudeData⟩
  rcases amplitudeData with ⟨hKg', amplitudeData⟩
  rcases amplitudeData with ⟨hKe, amplitudeData⟩
  rcases amplitudeData with ⟨heq, amplitudeData⟩
  rcases amplitudeData with ⟨hglobal, amplitudeData⟩
  rcases amplitudeData with ⟨hcover, amplitudeData⟩
  rcases amplitudeData with ⟨hQt, amplitudeData⟩
  rcases amplitudeData with ⟨hQs, amplitudeData⟩
  rcases amplitudeData with ⟨hQg, amplitudeData⟩
  rcases amplitudeData with ⟨hQb, amplitudeData⟩
  rcases amplitudeData with ⟨hQi, amplitudeData⟩
  rcases amplitudeData with ⟨hO, amplitudeData⟩
  rcases amplitudeData with ⟨hWave, amplitudeData⟩
  rcases amplitudeData with ⟨hBbase, amplitudeData⟩
  rcases amplitudeData with ⟨hD₁, amplitudeData⟩
  rcases amplitudeData with ⟨hD₂, amplitudeData⟩
  rcases amplitudeData with ⟨hD₃, amplitudeData⟩
  rcases amplitudeData with ⟨hD₄, amplitudeData⟩
  rcases amplitudeData with ⟨hD₅, amplitudeData⟩
  have hamp := amplitudeData
  have hKgEq : Kglobal = Kg := funext (fun p ↦ hglobal p)
  subst Kglobal
  have collarData := hphase eT eI buffer Rbase εcollar δT δI Hcollar
    hε hδT hδI χ hχ hχone hχsupport hχder ψ hψs
  rcases collarData with ⟨δT', collarData⟩
  rcases collarData with ⟨δI', collarData⟩
  rcases collarData with ⟨G, collarData⟩
  rcases collarData with ⟨hδT', collarData⟩
  rcases collarData with ⟨hδI', collarData⟩
  have hphase := collarData
  choose Cβ hCβ hcone using
    (fun p ↦ exists_selectedEndpointMultiplier_temporal_cone f p (hρb p) (hsrcρ p))
  have htpos : 0 < threshold := zero_lt_one.trans_le (f.radialThreshold_ge_one.trans ht)
  have hΔ (p : f.centers) : 0 ≤ 3*(f.chart p).maskRadius/4 := by
    have hmr := (f.chart p).maskRadius_pos
    positivity
  let ec := fun p : f.centers ↦ RegularSector.FiniteEvolution.physicalCoordinateIsometry (f.chart p).index
  let χom := fun p y ↦ (μ (ec p y) : ℂ) * endpointOutputMask f p output y
  let χsm := fun p y ↦ (ν (ec p y) : ℂ) * chartInputMask f p y
  have hec (p : f.centers) (y : E) : ec p y = physicalCoordinates (f.chart p).index y := rfl
  have hμchart p : ContDiff ℝ ∞ (μ ∘ ec p) := hμ.comp (ec p).contDiff
  have hνchart p : ContDiff ℝ ∞ (ν ∘ ec p) := hν.comp (ec p).contDiff
  have hχom p : ContDiff ℝ ∞ (χom p) :=
    (Complex.ofRealCLM.contDiff.comp (hμchart p)).mul (endpointOutputMask_properties f p ho hoc hout).1
  have hχsm p : ContDiff ℝ ∞ (χsm p) :=
    (Complex.ofRealCLM.contDiff.comp (hνchart p)).mul (chartPhysicalMasks_properties f p).2.1
  have hsubo p : tsupport (χom p) ⊆ tsupport (endpointOutputMask f p output) := tsupport_mul_subset_right
  have hsubs p : tsupport (χsm p) ⊆ tsupport (chartInputMask f p) := tsupport_mul_subset_right
  have hbound (p : f.centers) :=
    ResidualLocalization.UniformSupported.exists_supported_directResidual_integral_fourier_bound_of_uniform_masks
      (q := d+1) eT eI eu ez J hJ (-1) (3*(f.chart p).maskRadius/4) (hΔ p)
      order 0 0 0 0 0 0 0 c C b₀ hc ha₀ (by norm_num : (0 : ℝ) ≤ 1)
      (χom p) (χsm p) (selectedEndpointMultiplier f p threshold)
      (hχom p) (hχsm p)
      (selectedEndpointMultiplier_bounds f p threshold).1
      (endpointOutputMask_properties f p ho hoc hout).2.1.mul_left
      (chartPhysicalMasks_properties f p).2.2.2.1.mul_left (by norm_num : (0 : ℝ) ≤ 1)
      (hCβ p) (selectedEndpointMultiplier_bounds f p threshold).2
      (hcone p threshold htpos) Pbase Bbase O hPbase hBbase hO (hKjet p)
      (δT' p) (δI' p) (G p) (G p) (hδT' p) (hδI' p)
      P₀ Hcollar Wave O Qt Qs Qg Qb Qi hP₀ hQt hQs hQg hQb hQi hHcollar hWave hO
      (closedBall 0 Rbase) (isCompact_closedBall 0 Rbase) (ψ p) (hψ p) (hψs p) (hψb p)
      (θ p) (hθ p) (hθs p) (hθone p) D (hKg p)
  choose bLoss Cmq Cpair Creal hCmq hCpair hCreal hbound using hbound
  refine ⟨bLoss, Cmq, hCmq, ?_⟩
  intro Rstar hRstar L ρ hL hρ Q B hQ hB Φ Cchart angular h z Fs W
    hphaseSmooth hphaseBuffer hdiff hnear hphaseCost hang hW hFs hWs hphysical hsourceTime hseminorm
    Gext hGext hGgerm mif mof hmi hmo hmic hmoc hmirange hmorange
    hmisupp hmosupp hmiJets hmoJets hshort p mi mo Δ χout χsource β Ψoriginal
    Aoriginal Boriginal W₀original W₁original
    Treg hreal hrealAdj hm hmAdj LOW hLOW hlim hlimAdj Mi Mo Qop hMi hMo hQop Qm accuracy backward u
  obtain ⟨Ψ, g, hΨ, hΨon, hbase, hgerm, hnormalizedGerm, hnormalizedJets,
    hagree, hphysicalPhase, hg, hcomp, hcollars⟩ :=
    hphase Rstar hRstar L hL Q hQ h Φ Cchart hphaseSmooth hphaseBuffer hdiff hnear hphaseCost
  have hann (p : f.centers) : tsupport (mif p) ⊆ univ ×ˢ frequencyAnnulus a₀ b₀ :=
    fun _ hv ↦ ⟨mem_univ _, (hmisupp p hv).2⟩
  have hamp' := hamp mif mof (fun p ↦ (hmi p))
    (fun p ↦ (hmo p)) hmiJets hmoJets hann
    Rstar hRstar L ρ hL hρ Q B hQ hB Φ Cchart angular hang hW hFs hphysical hseminorm p
  obtain ⟨hbSmooth, hbNormalized, hbGlobal, hbPhysical, hprim, hwave, hoSlice, hcompAmp, hglobalSupport⟩ := hamp'
  obtain ⟨UT, UI, hε', hχ', hχone', hdomains⟩ := hcollars Gext hGext hGgerm mif mof hshort
    (fun p ↦ by rintro _ ⟨v, hv, rfl⟩; exact (hmisupp p hv).1) ρ hρ
  have hjet (u' y' : E) : elapsedOutputJetCarrier (Kjet p) mi mo u' y' ⊆
      elapsedOutputJetCarrier (Kelapsed p) mi mo u' y' := by
    intro v hv
    refine ⟨?_, hv.2⟩
    rw [heq p]
    exact hsub p hv.1
  have hsupp := hsupport p Q B (Φ p) (Cchart p) (angular p)
    (hang p) (hW p) (hphysical p) (hsourceTime p) (hFs p) (hWs p)
  have haux := selected_common_smooth_direct_residual f p (hρb p) (hsrcρ p)
    output hout Q B (W p) (hW p) (hphysical p)
  have hslab := selected_common_residual_retarded_buffer f p (hρb p) (hsrcρ p)
    output hout (Cchart p) (hsourceTime p) (W p 2) (hWs p)
  let Ac := fun y i ↦ chartOutputMask f p y • Aoriginal y i
  let Bc := fun y ↦ chartOutputMask f p y • Boriginal y
  let b := directRetardedAmplitudes Ac Bc W₀original W₁original true
  have hb : ∀ t s y η, s ≤ (z p).1 - (f.chart p).maskRadius/2 → b t s y η = 0 := by
    rw [show b = _ from haux.1]
    exact hslab.1
  obtain ⟨hiAnn, hiBound⟩ := selected_completeFactor_sliced_localizer_inputs
    (fun v hv ↦ (hmisupp p hv).2) (hmirange p)
  have hbasei : Prod.fst '' tsupport mi ⊆ closedBall 0 Rbase := by
    rintro _ ⟨v, hv, rfl⟩
    exact (hmisupp p hv).1
  have hbaseo : Prod.fst '' tsupport mo ⊆ closedBall 0 Rbase := by
    rintro _ ⟨v, hv, rfl⟩
    exact (hmosupp p hv).1
  have hmeasuredAmplitude (b' : TwoTimeAmplitude d (d+1)) (r : ℝ) (u v ξ : E) :
      elapsedAmplitude b' (χom p) (χsm p) β r u v ξ =
        ((μ (ec p u) : ℂ)*(ν (ec p v) : ℂ)) • elapsedAmplitude b' χout χsource β r u v ξ :=
    measured_orientedElapsedAmplitude_eq μ ν (ec p) b' χout χsource β false r u v ξ
  have hameq (r : ℝ) : elapsedAmplitude b (χom p) (χsm p) β r =
      elapsedAmplitude (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original true)
        (χom p) (χsm p) β r := by
    funext u v ξ
    simpa only [hmeasuredAmplitude] using congrArg
      (fun Ab : FullAmplitude (d+1) (d+1) ↦ ((μ (ec p u) : ℂ)*(ν (ec p v) : ℂ)) • Ab u v ξ)
      (hsupp.1 r)
  have hrawBound : ∀ r ∈ Icc 0 Δ, ∀ u ∈ tsupport χout, ∀ v ∈ tsupport χsource,
      ∀ ξ ∈ tsupport β, ‖b (u 0) (u 0-r) (spatialPart u) (spatialPart ξ)‖ ≤ Bbase 0 := by
    intro r hr u hu v hv ξ hξ
    have hmem := hphysicalMap p r hr ξ hξ (u,v) ⟨hu,hv⟩
    have hh := hbPhysical _ (hUabuffer p hmem) (hUapos p _ hmem) 0
    simp only [norm_iteratedFDeriv_zero, SymbolBudgets.elapsedPoint_eq,
      SymbolBudgets.jointAmplitude, pow_zero, mul_one] at hh
    change ‖b (u 0) (u 0-r) (spatialPart u) (spatialPart ξ)‖ ≤
      (1+‖spatialPart ξ‖) ^ (-1 : ℝ) * Bbase 0 at hh
    apply hh.trans
    exact mul_le_of_le_one_left (hBbase 0)
      (by rw [Real.rpow_neg_one]; exact inv_le_one_of_one_le₀ (le_add_of_nonneg_right (norm_nonneg _)))
  obtain ⟨hgraphMeasured, hLOWm, hrealM, hrealAdjM, hmM, hmAdjM, hlimM, hlimAdjM, hIntegralM⟩ :=
    measured_elapsedGraph_regularizations_of_supported_auxiliary Ψoriginal
      (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original true) χout χsource β
      (chartPhysicalMasks_properties f p).2.1 (selectedEndpointMultiplier_bounds f p threshold).1
      1 (selectedEndpointMultiplier_bounds f p threshold).2 Δ
      (Ψ p) b (hΨ p) hbSmooth (Bbase 0) hrawBound
      (fun r _ ↦ hsupp.1 r) (hagree p b) Treg hreal hrealAdj hm hmAdj LOW hLOW hlim hlimAdj
      (μ ∘ ec p) (ν ∘ ec p) (hμchart p) (hνchart p) (fun y ↦ hμb _) (fun y ↦ hνb _)
  have hphaseMeasured : ∀ r ∈ Icc 0 Δ, ∀ u v ξ,
      elapsedAmplitude b (χom p) (χsm p) β r u v ξ ≠ 0 →
        elapsedPhase (Ψ p) r u ξ = elapsedPhase Ψoriginal r u ξ := by
    intro r hr u v ξ hne
    apply hagree p b r hr u v ξ
    intro hz
    exact hne (by rw [hmeasuredAmplitude, hz, smul_zero])
  have hcarrierMeasured (r : ℝ) (ξ : E) :
      tsupport (fun w : E × E ↦ elapsedAmplitude b (χom p) (χsm p) β r w.1 w.2 ξ) ⊆
      tsupport (fun w : E × E ↦ elapsedAmplitude b χout χsource β r w.1 w.2 ξ) := by
    simp only [hmeasuredAmplitude]
    exact tsupport_smul_subset_right _ _
  have hresult := hbound p mi mo (hmi p) (hmo p)
    (hmorange p) (hmic p) (hmoc p)
    hiAnn hiBound Ψoriginal ρ L hρ hL Ac Bc W₀original W₁original true (Ψ p) (hΨ p)
    Aoriginal Boriginal W₀original W₁original hbSmooth
    (fun r _ ↦ hameq r) (Ua p) (Ua p) (hUa p) (hΨon p) (hbase p)
    (fun v hv j ↦ by simpa only [Nat.add_zero] using hbPhysical v (hUabuffer p hv) (hUapos p v hv) j)
    (fun r hr _ _ ξ _ v hv hβ ↦ hphysicalMap p r hr (ρ • ξ) (subset_tsupport _ hβ) v ⟨hsubo p hv.1, hsubs p hv.2⟩)
    (by simpa only [Nat.add_zero] using hoSlice)
    (fun bw y hy ↦ hψmask p bw y (by
      cases bw <;> first | exact hsubo p hy | exact hsubs p hy)) (fun y hy ↦ hψY p y (hbaseo hy)) hbasei
    hphaseMeasured
    (fun bw y _ low j l hc ↦ (measured_jointElapsedAmplitude_tsupport_subset μ ν (ec p) b
      χout χsource β bw ρ mi (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff l) 0 y (θ p)).trans
        (hsupp.2 mi mo univ (hann p) bw ρ hρ low j l hc y).1)
    ((z p).1 - (f.chart p).maskRadius/2)
    ((z p).1 - (f.chart p).maskRadius/2 + 3*(f.chart p).maskRadius/4)
    hb (fun u hu ↦ by change (μ (ec p u) : ℂ) * χout u = 0; have hz : χout u = 0 := hslab.2.1 u hu; rw [hz, mul_zero]) hslab.2.2.le
    (fun _ _ _ ↦ χ) (UT p) (UI p) (εcollar/4) hε'
    (fun _ _ _ _ _ ↦ hχ')
    (fun bw u' hu y' hy ↦ (hdomains p bw u' hu y' hy).1)
    (fun bw u' hu y' hy ↦ (hdomains p bw u' hu y' hy).2.1)
    (fun _ _ _ _ _ ↦ hχone')
    (fun bw u' hu y' hy ↦ (hdomains p bw u' hu y' hy).2.2.1)
    (fun bw u' hu y' hy ↦ (hdomains p bw u' hu y' hy).2.2.2.1)
    (fun bw u' hu y' hy r hr v hv ↦ ((hdomains p bw u' hu y' hy).2.2.2.2.1 r hr v hv).1)
    (fun bw u' hu y' hy r hr v hv ↦ ((hdomains p bw u' hu y' hy).2.2.2.2.1 r hr v hv).2)
    (fun bw u' hu y' hy v hv ↦ ((hdomains p bw u' hu y' hy).2.2.2.2.2.1 v hv).1)
    (fun bw u' hu y' hy v hv ↦ ((hdomains p bw u' hu y' hy).2.2.2.2.2.1 v hv).2)
    (fun u' hu y' hy ↦ (hdomains p false u' hu y' hy).2.2.2.2.2.2.2)
    (fun bw u' hu y' hy ↦ (hdomains p bw u' hu y' hy).2.2.2.2.2.2.1)
    (fun u' _ y' _ v hv j ↦ (hwave u' y' v (hjet u' y' hv) j).1)
    (fun u' _ y' _ v hv j ↦ by simpa only [Nat.add_zero] using (hwave u' y' v (hjet u' y' hv) j).2)
    (fun u' _ y' _ v hv j ↦ by simpa only [Nat.add_zero, χom, χsm, hec, mi] using hprim u' y' v (hjet u' y' hv) j)
    (fun _ ↦ Vphase p) (fun _ ↦ Kphysical p) (g p)
    (fun _ _ ↦ hVphase p) (fun _ _ ↦ hKphysical p) (fun _ _ ↦ hKV p)
    (hphysicalPhase p)
    (fun r hr low j ξ hξ w hw ↦ hcarrier p b ρ (zero_lt_one.trans_le hρ).ne'
      r hr low j ξ hξ w (hcarrierMeasured r (ρ • ξ) hw))
    (hg p) (hcomp p) hcompAmp
    (fun bw low j l hc r _ y ↦ (hglobalSupport bw low j l hc y).1 r)
    (tsupport β) (isClosed_tsupport β)
    (zero_notMem_selectedEndpointMultiplier_tsupport f p
      (zero_lt_one.trans_le (f.radialThreshold_ge_one.trans ht)))
    (subset_refl _) complexPhysicalCutoff (fun _ _ _ ↦ rfl)
    (fun j r ↦ measuredOperator (μ ∘ ec p) (ν ∘ ec p)
      (hμchart p).continuous (hνchart p).continuous (fun y ↦ hμb _) (fun y ↦ hνb _) (Treg j r))
    hrealM hrealAdjM hmM hmAdjM hLOWm hlimM hlimAdjM Mi Mo Qm hMi hMo (hIntegralM Qop hQop)
  simpa only [max_eq_left (by norm_num : (-1 : ℝ) ≤ 0), zero_add] using
    hresult.2.2.2.1 accuracy backward u

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
