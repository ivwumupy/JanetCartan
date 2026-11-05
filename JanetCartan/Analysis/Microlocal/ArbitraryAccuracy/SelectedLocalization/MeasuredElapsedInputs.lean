module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.UniformElapsedAmplitudeInputs
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.MeasuredElapsedProfiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.MeasuredElapsedMasks

/-!
# Actual selected measured elapsed-amplitude inputs

Apply the existing retained amplitude producer and fixed measurement profiles
on the same charts, symbols, elapsed carriers and proof localizers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly RegularSector.FinitePdo
open Characteristic Characteristic.AmplitudeBounds Characteristic.ConicAmplitude
open Characteristic.ConicPhase Characteristic.ResidualCoordinates
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open Characteristic.EvolutionIntegral.KernelIdentification Characteristic.UniformEvolution
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open EvolutionLocalization EvolutionIntegratedLocalization FourierIntegral FiniteChain.Graph
open FiniteChain.Graph.PhysicalShells
open FiniteChain.Graph.KernelEstimates FiniteChain.Graph.PhysicalShells.Noncomparable
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Z" => RootState (Euclidean d)
local notation "V" => ℝ × JointVariables E
local notation "Mat" => MetricTensor (d+1)

/-- Apply the actual retained elapsed-amplitude producer to the original two
measurement masks in every physical chart. The same carriers, residual symbols,
full zeroth-order field, radial threshold, elapsed intervals and proof localizers
are retained. Constants precede the varying coefficients, history and proof masks.
This supplies the measured primitive mask/comparable/support inputs of the
supported leakage deduction (`app:ch_regular:eq:high-amplitude`,
`app:ch_regular:eq:chain-tail`, `app:ch_regular_base:eq:measured-adjoint`). -/
theorem exists_selected_measured_elapsed_amplitude_inputs_of_joint_localizer_profile
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hρb : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (c C a₀ b₀ : ℝ) (ha₀ : 0 < a₀)
    (ra rb : f.centers → ℝ) (hra : ∀ p, 0 < ra p) (hab : ∀ p, ra p ≤ rb p)
    (cost : f.centers → ℕ → ℝ) (hcost : ∀ p m, 0 < cost p m)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (threshold : ℝ) (hthreshold : f.radialThreshold ≤ threshold)
    (Δ : f.centers → ℝ) (θ : f.centers → ℝ → ℂ)
    (hθ : ∀ p, HasCompactSupport (θ p))
    (hθone : ∀ p, ∀ r ∈ Icc 0 (Δ p), θ p r = 1)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (Hmask : ℕ → ℝ) (hHmask : ∀ j, 0 ≤ Hmask j) :
    ∃ Kglobal : f.centers → Set (JointVariables E),
    ∃ Kelapsed : f.centers → Set V,
    ∃ Qt Qs Qg Qb Qi O Wave Bbase : ℕ → ℝ, ∃ D : AmplitudeProfiles,
      (∀ p, IsCompact (Kglobal p)) ∧ (∀ p, IsCompact (Kelapsed p)) ∧
      (∀ p, Kelapsed p = tsupport (θ p) ×ˢ Kglobal p) ∧
      (∀ p, Kglobal p = Comparable.comparableJointCarrier c C a₀ b₀
        (elapsedComparableCarrier (endpointOutputMask f p output)
          (selectedEndpointMultiplier f p threshold) univ c C a₀ b₀)
        (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p))
        (frequencyAnnulus a₀ b₀)) ∧
      (∀ p, Icc 0 (Δ p) ×ˢ Kglobal p ⊆ Kelapsed p) ∧
      (∀ j, 0 ≤ Qt j) ∧ (∀ j, 0 ≤ Qs j) ∧ (∀ j, 0 ≤ Qg j) ∧
      (∀ j, 0 ≤ Qb j) ∧ (∀ j, 0 ≤ Qi j) ∧ (∀ j, 0 ≤ O j) ∧
      (∀ j, 0 ≤ Wave j) ∧ (∀ j, 0 ≤ Bbase j) ∧
      D.symbolOffset = 0 ∧ D.graphCutoffOffset = 0 ∧ D.outputCutoffOffset = 0 ∧
      D.inputMaskOffset = 0 ∧ D.outputMaskOffset = 0 ∧
      ∀ (mi mo : f.centers → LocalizerSymbol (d+1)),
      (∀ p, ContDiff ℝ ∞ (mi p)) → (∀ p, ContDiff ℝ ∞ (mo p)) →
      (∀ p j z, ‖iteratedFDeriv ℝ j (mi p) z‖ ≤ Hmask j) →
      (∀ p j z, ‖iteratedFDeriv ℝ j (mo p) z‖ ≤ Hmask j) →
      (∀ p, tsupport (mi p) ⊆ univ ×ˢ frequencyAnnulus a₀ b₀) →
      ∀ (Rstar : ℕ), 10 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Fin (d+1) → Mat) (B : E → Mat),
      (∀ j, cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j - Rstar)) →
      (∀ j, cNorm (closedBall x RQ) j B ≤ A j * L ^ (j - Rstar)) →
      ∀ (Φ : f.centers → Z × ℝ → Z) (Cchart : f.centers → OpenPartialHomeomorph T T)
        (angular : f.centers → Euclidean d → ℝ),
      let Fs := fun p ↦ selectedBufferedAmplitude f p Q B (Φ p) (Cchart p)
      let W := fun p (j : Fin 3) ↦
        collared (f.chart p).radialSection (if j=0 then 0 else 1) (angular p) (Fs p j)
      let J := fun p ↦
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius/2) (ra p) (rb p)
      (∀ p, ∀ η ∈ tsupport (angular p), 0 < (f.chart p).radialSection η) →
      (∀ p j, ContDiff ℝ ∞ (W p j)) →
      (∀ p,
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        tsupport (Fs p 2) ⊆ closedBall (z.1, z) ((f.chart p).bufferRadius/2)) →
      (∀ p (v : T), (f.chart p).timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) →
        ∀ j : Fin (d+1), (fun k ↦ W p 2 v k j) =
          WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
            (fun y k ↦ W p 1
              (physicalSlice (coordinateSplit (f.chart p).index) v.2.1 v.2.2.2 y) k j)
            ((coordinateSplit (f.chart p).index).symm (v.1, v.2.2.1))) →
      (∀ p j m, BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m
          (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) j) ∧
        twoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m
          (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) j) ≤
          cost p m * (1+cNorm (closedBall x RQ) (m+10) Q+cNorm (closedBall x RQ) (m+9) B)) →
      ∀ p,
        let Aoriginal := fun y i ↦ (coefficient (f.chart p).index Q y i).map Complex.ofReal
        let Boriginal := fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal
        let Ac := fun y i ↦ chartOutputMask f p y • Aoriginal y i
        let Bc := fun y ↦ chartOutputMask f p y • Boriginal y
        let b := directRetardedAmplitudes Ac Bc
          (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) 0)
          (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) 1) true
        let χout := fun y ↦ (μ (physicalCoordinates (f.chart p).index y) : ℂ) *
          endpointOutputMask f p output y
        let χsource := fun y ↦ (ν (physicalCoordinates (f.chart p).index y) : ℂ) *
          chartInputMask f p y
        ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude b) ∧
        (∀ v ∈ Kelapsed p, ∀ j,
          ‖iteratedFDeriv ℝ j (normalizedElapsedSymbol ρ b) v‖ ≤ ρ ^ (-1 : ℝ) * Qb j * L ^ j) ∧
        (∀ r ∈ Icc 0 (Δ p), ∀ v ∈ Kglobal p, ∀ j,
          ‖iteratedFDeriv ℝ j (normalizedElapsedSymbol ρ b) (r, v)‖ ≤
            ρ ^ (-1 : ℝ) * Qb j * L ^ j) ∧
        (∀ w ∈ bufferedBase
            ((coordinateSplit (f.chart p).index x).1,
              ((coordinateSplit (f.chart p).index x).2, (coordinateSplit (f.chart p).index p.val.val).2))
            (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius) ×ˢ
              angularCone (f.chart p).radialSection (coordinateSplit (f.chart p).index p.val.val).2
                (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius),
          (1/2 : ℝ) < ‖w.2‖ → ∀ j,
            ‖iteratedFDeriv ℝ j (SymbolBudgets.jointAmplitude b) w‖ ≤
              (1+‖w.2‖) ^ (-1 : ℝ) * Bbase j * L ^ j) ∧
        (∀ u y, ∀ v ∈ elapsedOutputJetCarrier (Kelapsed p) (mi p) (mo p) u y, ∀ j,
          ‖iteratedFDeriv ℝ j (fun w : V ↦ χout w.2.1.1) v‖ ≤
            Qt j * L ^ j ∧
          ‖iteratedFDeriv ℝ j (fun w : V ↦ χsource w.2.1.2) v‖ ≤ Qs j * L ^ j ∧
          ‖iteratedFDeriv ℝ j (fun w : V ↦ selectedEndpointMultiplier f p threshold (ρ • w.2.2.1)) v‖ ≤
            Qg j * L ^ j ∧
          ‖iteratedFDeriv ℝ j (normalizedElapsedSymbol ρ b) v‖ ≤ ρ ^ (-1 : ℝ) * Qb j * L ^ j ∧
          ‖iteratedFDeriv ℝ j (fun w : V ↦ (mi p (y, w.2.2.2.1) : ℂ)) v‖ ≤ Qi j * L ^ j) ∧
        (∀ u y, ∀ v ∈ elapsedOutputJetCarrier (Kelapsed p) (mi p) (mo p) u y, ∀ j,
          ‖iteratedFDeriv ℝ j outputJointWave (0, v.2.2.2.2)‖ ≤ Wave j ∧
          ‖iteratedFDeriv ℝ j (mo p) (u, v.2.2.2.2)‖ ≤ O j * L ^ j) ∧
        (∀ u ζ j, ‖iteratedFDeriv ℝ j (fun t ↦ mo p (t, ζ)) u‖ ≤ O j * L ^ j) ∧
        (∀ backward low j k, IsComparablePair c C a₀ b₀ ρ low j k →
          ∀ r ∈ Icc 0 (Δ p), ∀ y,
          HasAmplitudeGrades D ρ (ρ ^ (-1 : ℝ)) L
            (orientedElapsedAmplitude backward b χout
              χsource (selectedEndpointMultiplier f p threshold) r)
            (mi p) (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y (Kglobal p)) ∧
        ∀ backward low j k, IsComparablePair c C a₀ b₀ ρ low j k → ∀ y,
          (∀ r, tsupport (FiniteChain.Graph.jointAmplitude ρ
            (orientedElapsedAmplitude backward b χout
              χsource (selectedEndpointMultiplier f p threshold) r)
            (mi p) (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y) ⊆ Kglobal p) ∧
          tsupport (fun v : V ↦ θ p v.1 • jointElapsedAmplitude backward ρ b
            χout χsource
            (selectedEndpointMultiplier f p threshold) (mi p) (fun _ ↦ 0)
            (graphBranchCutoff low j) (outputCutoff k) 0 y v) ⊆ Kelapsed p := by
  obtain ⟨Kg, Ke, Qt, Qs, Qg, Qb, Qi, O, Wave, Bbase, D,
    hKg, hKe, heq, hglobal, hcover, hQt, hQs, hQg, hQb, hQi, hO, hWave, hBbase,
    hD₁, hD₂, hD₃, hD₄, hD₅, hamp⟩ :=
    exists_selected_elapsed_amplitude_inputs_of_joint_localizer_profile f hρb hsrcρ
      c C a₀ b₀ ha₀ ra rb hra hab cost hcost A hA output ho hoc hout threshold hthreshold
      Δ θ hθ hθone Hmask hHmask
  obtain ⟨Qtm, Qsm, hQtm, hQsm, hmeasuredMasks⟩ :=
    exists_measured_elapsed_mask_profiles μ ν hμ hν hμc hνc Qt Qs hQt hQs
  obtain ⟨Dm, hDm₁, hDm₂, hDm₃, hDm₄, hDm₅, _, hmeasuredGrades⟩ :=
    exists_measured_elapsed_comparable_profiles (q := d+1) μ ν hμ hν hμc hνc D
  refine ⟨Kg, Ke, Qtm, Qsm, Qg, Qb, Qi, O, Wave, Bbase, Dm,
    hKg, hKe, heq, hglobal, hcover, hQtm, hQsm, hQg, hQb, hQi, hO, hWave, hBbase,
    hDm₁.trans hD₁, hDm₂.trans hD₂, hDm₃.trans hD₃, hDm₄.trans hD₄, hDm₅.trans hD₅, ?_⟩
  intro mi mo hi hom hmi hmo hAnn Rstar hRstar L ρ hL hρ Q B hQ hB Φ Cchart angular
    Fs W J hang hW hFs hphysical hbudget p Aoriginal Boriginal Ac Bc b χout χsource
  obtain ⟨hs, hn, ht, hp, hprim, hwave, hoSlice, hg, hsupp⟩ :=
    hamp mi mo hi hom hmi hmo hAnn Rstar hRstar L ρ hL hρ Q B hQ hB Φ Cchart angular
      hang hW hFs hphysical hbudget p
  let ec := RegularSector.FiniteEvolution.physicalCoordinateIsometry (f.chart p).index
  have hec (w : E) : ec w = physicalCoordinates (f.chart p).index w := rfl
  have hχout := (endpointOutputMask_properties f p ho hoc hout).1
  have hχsource := (chartPhysicalMasks_properties f p).2.1
  refine ⟨hs, hn, ht, hp, ?_, hwave, hoSlice, ?_, ?_⟩
  · intro u y v hv j
    have ht' (w) (hw : w ∈ elapsedOutputJetCarrier (Ke p) (mi p) (mo p) u y) k :=
      (hprim u y w hw k).1
    have hs' (w) (hw : w ∈ elapsedOutputJetCarrier (Ke p) (mi p) (mo p) u y) k :=
      (hprim u y w hw k).2.1
    have hm := hmeasuredMasks ec L hL (endpointOutputMask f p output) (chartInputMask f p)
      hχout hχsource 0 0 (elapsedOutputJetCarrier (Ke p) (mi p) (mo p) u y)
      (by simpa only [Nat.add_zero] using ht') (by simpa only [Nat.add_zero] using hs') v hv j
    refine ⟨?_, ?_, (hprim u y v hv j).2.2⟩
    · simpa only [Nat.add_zero, χout, hec] using hm.1
    · simpa only [Nat.add_zero, χsource, hec] using hm.2
  · intro backward low j k hpair r hr y
    exact hmeasuredGrades ec b (endpointOutputMask f p output) (chartInputMask f p)
      (selectedEndpointMultiplier f p threshold) backward r ρ (ρ ^ (-1 : ℝ)) L hL
      (mi p) (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y (Kg p)
      (hg backward low j k hpair r hr y)
  · intro backward low j k hpair y
    constructor
    · intro r
      exact (measured_elapsed_jointAmplitude_tsupport_subset μ ν ec b
        (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointMultiplier f p threshold) backward r ρ (mi p) (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y).trans
        ((hsupp backward low j k hpair y).1 r)
    · exact (measured_jointElapsedAmplitude_tsupport_subset μ ν ec b
        (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointMultiplier f p threshold) backward ρ (mi p) (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y (θ p)).trans
        (hsupp backward low j k hpair y).2

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
