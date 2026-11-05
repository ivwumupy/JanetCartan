module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.ResidualGeometry

/-!
# The retained phase carrier for the actual selected direct residual

Intersect the actual compact comparable carrier with the projection of the
bounded dilations for its normalized `PW₁` symbol. The original amplitude
is unchanged, so the restriction also holds for every joint derivative
of every output jet in both orientations. The required phase radii are
chosen before the coefficients, shell, request or history.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
open SelectedLocalization
open RegularSector RegularSector.FiniteAssembly RegularSector.Characteristic
open RegularSector.FinitePdo
open Characteristic.ConicPhase Characteristic.ConicAmplitude Characteristic.UniformEvolution
open Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open Characteristic.EvolutionIntegral.KernelIdentification Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open EvolutionLocalization EvolutionIntegratedLocalization FourierIntegral
open FiniteChain.Graph FiniteChain.Graph.PhysicalShells
open FiniteChain.Graph.PhysicalShells.Noncomparable
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Z" => RootState (Euclidean d)
local notation "V" => ℝ × JointVariables E
local notation "Mat" => MetricTensor (d+1)

/-- Choose the bounded dilations, hence the undilated phase radii
`ra p / thi, ra p / tlo`, on the SAME actual family. The compact `Kjet`
simultaneously supplies the primitive Fourier estimate's `hs` and the
position, radial and clock data for its open collar sets. The selected
producer below identifies the smooth common-mask residual with the
original in elapsed amplitude, before either orientation is taken.
Consumer: `exists_directResidual_integral_fourier_bound_of_primitive_grades`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_direct_residual_phase_carriers
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hρb : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (c C a₀ b₀ : ℝ) (ha₀ : 0 < a₀)
    (ra rb : f.centers → ℝ) (hra : ∀ p, 0 < ra p) (hab : ∀ p, ra p ≤ rb p) :
    ∃ tlo thi : ℝ, 0 < tlo ∧ 0 < thi ∧
      ∀ output : E → ℝ, ContDiff ℝ ∞ output → HasCompactSupport output →
      tsupport output ⊆ ball x f.physicalRadius →
      ∀ threshold, f.radialThreshold ≤ threshold →
      ∀ θ : ℝ → ℂ, HasCompactSupport θ →
      let Kglobal p := selectedResidualComparableCarrier f p output threshold c C a₀ b₀
      let Kelapsed p := tsupport θ ×ˢ Kglobal p
      let Kjet p := selectedRetainedResidualCarrier f p output threshold c C a₀ b₀ θ
        (ra p) (rb p) tlo thi
      (∀ p, IsCompact (Kglobal p)) ∧ (∀ p, IsCompact (Kelapsed p)) ∧
      (∀ p, IsCompact (Kjet p)) ∧
      (∀ p, Kjet p ⊆ Kelapsed p) ∧
      (∀ p (v : V), v ∈ Kjet p →
        let lc := f.chart p
        let e := coordinateSplit lc.index
        v.2.1.1 0 ∈ closedBall (e x).1 (lc.maskRadius / 2) ∧
          spatialPart v.2.1.1 ∈ closedBall (e x).2 (lc.maskRadius / 2) ∧
          spatialPart v.2.2.1 ∈ radialSectionBand lc.radialSection (e p.val.val).2
            (lc.maskRadius / 2) (ra p / thi) (ra p / tlo) ∧
          |v.2.1.1 0 - v.2.1.2 0| ≤ 4 * f.physicalRadius) ∧
      ∀ p (Q : E → Fin (d+1) → Mat) (B : E → Mat)
        (Φ : Z × ℝ → Z) (Cchart : OpenPartialHomeomorph T T) (angular : Euclidean d → ℝ),
      let lc := f.chart p
      let e := coordinateSplit lc.index
      let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
      let Fs := selectedBufferedAmplitude f p Q B Φ Cchart
      let W := fun j : Fin 3 ↦ collared lc.radialSection (if j=0 then 0 else 1) angular (Fs j)
      let Aoriginal := fun y i ↦ (coefficient lc.index Q y i).map Complex.ofReal
      let Boriginal := fun y ↦ (zeroth lc.index B y).map Complex.ofReal
      let Ac := fun y i ↦ chartOutputMask f p y • Aoriginal y i
      let Bc := fun y ↦ chartOutputMask f p y • Boriginal y
      let b := directRetardedAmplitudes Ac Bc
        (selectedConicAmplitude f p Q B Φ Cchart angular 0)
        (selectedConicAmplitude f p Q B Φ Cchart angular 1) true
      let borig := directRetardedAmplitudes Aoriginal Boriginal
        (selectedConicAmplitude f p Q B Φ Cchart angular 0)
        (selectedConicAmplitude f p Q B Φ Cchart angular 1) true
      (∀ η ∈ tsupport angular, 0 < lc.radialSection η) →
      (∀ j, ContDiff ℝ ∞ (W j)) →
      (∀ v : T, lc.timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) →
        ∀ j : Fin (d+1), (fun k ↦ W 2 v k j) =
          WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
            (fun y k ↦ W 1 (physicalSlice e v.2.1 v.2.2.2 y) k j)
            (e.symm (v.1, v.2.2.1))) →
      (∀ v ∈ Cchart.target, (Cchart.symm v).2.1 = v.2.1) →
      tsupport (Fs 2) ⊆ closedBall (z.1, z) (lc.bufferRadius/2) →
      tsupport (W 2) ⊆ ConicPhase.domain lc.radialSection
        (Cchart.target ∩ Cchart.symm ⁻¹' (ball z.1 (lc.maskRadius/2) ×ˢ
          (ball z.1 (lc.maskRadius/2) ×ˢ ball z.2 (lc.maskRadius/2)))) →
      (∀ r, elapsedAmplitude b (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointMultiplier f p threshold) r =
        elapsedAmplitude borig
          (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointMultiplier f p threshold) r) ∧
      ∀ (mi mo : LocalizerSymbol (d+1)) (Ki : Set E),
        tsupport mi ⊆ Ki ×ˢ frequencyAnnulus a₀ b₀ →
        ∀ (backward : Bool) ρ, 1 ≤ ρ → ∀ low j k,
        IsComparablePair c C a₀ b₀ ρ low j k → ∀ y,
          tsupport (fun v : V ↦ θ v.1 • jointElapsedAmplitude backward ρ b
            (endpointOutputMask f p output) (chartInputMask f p)
            (selectedEndpointMultiplier f p threshold) mi (fun _ ↦ 0)
            (graphBranchCutoff low j) (outputCutoff k) 0 y v) ⊆ Kjet p ∧
          ∀ (Ψ Ψorig : TwoTimePhase d) x', ContDiff ℝ ∞ mo → ∀ m (v : Fin m → E),
            cutElapsedOutputJetAmplitude backward ρ Ψ b
              (endpointOutputMask f p output) (chartInputMask f p)
              (selectedEndpointMultiplier f p threshold) mi mo
              (graphBranchCutoff low j) (outputCutoff k) θ x' y m v =
            cutElapsedOutputJetAmplitude backward ρ Ψorig borig
              (endpointOutputMask f p output) (chartInputMask f p)
              (selectedEndpointMultiplier f p threshold) mi mo
              (graphBranchCutoff low j) (outputCutoff k) θ x' y m v ∧
            ∀ D, tsupport (iteratedFDeriv ℝ D (cutElapsedOutputJetAmplitude backward ρ Ψorig borig
              (endpointOutputMask f p output) (chartInputMask f p)
              (selectedEndpointMultiplier f p threshold) mi mo
              (graphBranchCutoff low j) (outputCutoff k) θ x' y m v)) ⊆
              elapsedOutputJetCarrier (Kjet p) mi mo x' y := by
  obtain ⟨tlo, thi, hlo, hhi, hfamily⟩ :=
    exists_selected_direct_residual_carriers f hρb hsrcρ c C a₀ b₀ ha₀ ra rb hra hab
  refine ⟨tlo, thi, hlo, hhi, ?_⟩
  intro output ho hoc hout threshold ht θ hθ
  obtain ⟨Kg, Ke, hKg, hKe, _, hKeq, hKeqg, hs, hres⟩ :=
    hfamily output ho hoc hout threshold ht θ hθ
  intro Kglobal Kelapsed Kjet
  have heg : Kg = Kglobal := funext hKeqg
  have he : Ke = Kelapsed := funext fun p ↦ (hKeq p).trans (congrArg (fun K ↦ tsupport θ ×ˢ K) (hKeqg p))
  subst Kg Ke
  refine ⟨hKg, hKe, fun p ↦ (isCompact_retainedResidualJetCarrier (hKe p) ..).inter_right
    (isClosed_le continuous_fst continuous_const), fun _ _ hv ↦ hv.1.1, ?_, ?_⟩
  · intro p v hv
    obtain ⟨hvT, hvY, hvclock⟩ := selectedResidualComparableCarrier_positions f p hout hv.1.1.2
    exact ⟨hvT, hvY, retainedResidualJetCarrier_phase_band f p ht hlo (hra p) le_rfl le_rfl hv.1,
      hvclock⟩
  · intro p Q B Φ Cchart angular lc e zp Fs W Aoriginal Boriginal Ac Bc b borig
      hang hW hphysical hsourceTime hFs hWs
    obtain ⟨_, _, hid, hbsource, hupper, hslab, hjet⟩ := hres p Q B Φ Cchart angular hang hW hphysical
      hsourceTime hFs hWs
    refine ⟨hid, ?_⟩
    intro mi mo Ki hmi backward ρ hρ low j k hp y
    have hρ' := zero_lt_one.trans_le hρ
    have hs' := (hs p mi (fun _ ↦ 0) Ki hmi b backward ρ hρ low j k hp 0 y).2
    have hrad := tsupport_cut_jointElapsedAmplitude_subset_retainedResidualJetCarrier
      (hKe p) lc.radialSection zp (lc.bufferRadius/2) (ra p) (rb p) tlo thi backward ρ b
      (endpointOutputMask f p output) (chartInputMask f p) (selectedEndpointMultiplier f p threshold)
      mi (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) θ 0 y hs' (fun v hv ↦
        ⟨(hjet v hv).2.1, (hjet v hv).2.2.1, (hjet v hv).2.2.2 ρ hρ' 0⟩)
    have htime : tsupport (fun v : V ↦ θ v.1 • jointElapsedAmplitude backward ρ b
        (endpointOutputMask f p output) (chartInputMask f p) (selectedEndpointMultiplier f p threshold)
        mi (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y v) ⊆
        {v | v.1 ≤ 3 * lc.maskRadius / 4} := by
      apply closure_minimal _ (isClosed_le continuous_fst continuous_const)
      intro v hv
      by_contra! hn
      change ¬ v.1 ≤ 3 * lc.maskRadius / 4 at hn
      have hz := jointElapsedAmplitude_eq_zero_above_slab backward ρ b (endpointOutputMask f p output)
        (chartInputMask f p) (selectedEndpointMultiplier f p threshold) mi (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y
        hbsource hupper (hslab.le.trans (le_of_not_ge hn)) v.2
      exact hv ((congrArg (fun A ↦ θ v.1 • A) hz).trans (smul_zero _))
    have hsharp := subset_inter hrad htime
    refine ⟨hsharp, ?_⟩
    intro Ψ Ψorig x' hmo m v
    have he := cutElapsedOutputJetAmplitude_eq_of_elapsedAmplitude_eq backward hρ'.ne' Ψ Ψorig
      b borig _ _ _ hid mi mo (graphBranchCutoff low j) (outputCutoff k) θ x' y hmo m v
    refine ⟨he, ?_⟩
    intro D
    rw [← he]
    exact tsupport_iteratedFDeriv_cutElapsedOutputJetAmplitude_subset_retained backward hρ'.ne'
        Ψ b _ _ _ mi mo _ _ θ x' y hmo hsharp m v D

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
