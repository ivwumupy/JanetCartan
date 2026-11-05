module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.NormalizedResidual
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.PhysicalAmplitude
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Comparable
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.ResidualCarriers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OutputJets

/-!
# Assembly of the selected elapsed amplitude profiles

The actual normalized residual profile instantiates the comparable estimate,
while the physical profile controls the full direct residual. A single set
of profiles covers the literal masks, localizers, both orientations, and
compact support. `AmplitudeInputs` restricts this assembly to each chart's
own buffered elapsed cutoff.
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

/-- Assemble the normalized residual, physical residual, literal mask, localizer,
and comparable profiles on the SAME direct residual and the SAME compact carriers.
Every analytic premise is an original coefficient profile or a retained field of
`RegularSector.FiniteAssembly.exists_finite_direct_operator_bounds`. The input
annulus and buffered localizers are supplied by
`ProtectedMasks.exists_uniform_conic_nested_localization_data`.

This discharges `hprimitiveMasks`, `hw`, `hmo`, `hoBound`, `hglobalGrades`,
`hglobalSupport`, and `hs` of `CompleteFactor`; the physical estimate restricts
to its actual `Ua` by `exists_selected_elapsed_physical_carriers`. The
normalized residual premise of the comparable deduction is instantiated here.
Both orientations retain order minus one and all offsets are zero. Constants
precede current coefficients, slow scale, frequency and accuracy
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_selected_completeFactor_amplitude_inputs
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
    (Δ : ℝ) (θ : ℝ → ℂ) (hθ : HasCompactSupport θ)
    (hθone : ∀ r ∈ Icc 0 Δ, θ r = 1)
    (mi mo : f.centers → LocalizerSymbol (d+1))
    (Ki Ii Ko Oo : f.centers → Set (E × E))
    (hi : ∀ p, IsBufferedLocalizer (mi p) (Ki p) (Ii p))
    (hmo : ∀ p, IsBufferedLocalizer (mo p) (Ko p) (Oo p))
    (hAnn : ∀ p, tsupport (mi p) ⊆ univ ×ˢ frequencyAnnulus a₀ b₀) :
    ∃ Kglobal : f.centers → Set (JointVariables E),
    ∃ Kelapsed : f.centers → Set V,
    ∃ Qt Qs Qg Qb Qi O Wave Bbase : ℕ → ℝ, ∃ D : AmplitudeProfiles,
      (∀ p, IsCompact (Kglobal p)) ∧ (∀ p, IsCompact (Kelapsed p)) ∧
      (∀ p, Kelapsed p = tsupport θ ×ˢ Kglobal p) ∧
      (∀ p, Kglobal p = Comparable.comparableJointCarrier c C a₀ b₀
        (elapsedComparableCarrier (endpointOutputMask f p output)
          (selectedEndpointMultiplier f p threshold) univ c C a₀ b₀)
        (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p))
        (frequencyAnnulus a₀ b₀)) ∧
      (∀ p, Icc 0 Δ ×ˢ Kglobal p ⊆ Kelapsed p) ∧
      (∀ j, 0 ≤ Qt j) ∧ (∀ j, 0 ≤ Qs j) ∧ (∀ j, 0 ≤ Qg j) ∧
      (∀ j, 0 ≤ Qb j) ∧ (∀ j, 0 ≤ Qi j) ∧ (∀ j, 0 ≤ O j) ∧
      (∀ j, 0 ≤ Wave j) ∧ (∀ j, 0 ≤ Bbase j) ∧
      D.symbolOffset = 0 ∧ D.graphCutoffOffset = 0 ∧ D.outputCutoffOffset = 0 ∧
      D.inputMaskOffset = 0 ∧ D.outputMaskOffset = 0 ∧
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
        ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude b) ∧
        (∀ v ∈ Kelapsed p, ∀ j,
          ‖iteratedFDeriv ℝ j (normalizedElapsedSymbol ρ b) v‖ ≤ ρ ^ (-1 : ℝ) * Qb j * L ^ j) ∧
        (∀ r ∈ Icc 0 Δ, ∀ v ∈ Kglobal p, ∀ j,
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
          ‖iteratedFDeriv ℝ j (fun w : V ↦ endpointOutputMask f p output w.2.1.1) v‖ ≤
            Qt j * L ^ j ∧
          ‖iteratedFDeriv ℝ j (fun w : V ↦ chartInputMask f p w.2.1.2) v‖ ≤ Qs j * L ^ j ∧
          ‖iteratedFDeriv ℝ j (fun w : V ↦ selectedEndpointMultiplier f p threshold (ρ • w.2.2.1)) v‖ ≤
            Qg j * L ^ j ∧
          ‖iteratedFDeriv ℝ j (normalizedElapsedSymbol ρ b) v‖ ≤ ρ ^ (-1 : ℝ) * Qb j * L ^ j ∧
          ‖iteratedFDeriv ℝ j (fun w : V ↦ (mi p (y, w.2.2.2.1) : ℂ)) v‖ ≤ Qi j * L ^ j) ∧
        (∀ u y, ∀ v ∈ elapsedOutputJetCarrier (Kelapsed p) (mi p) (mo p) u y, ∀ j,
          ‖iteratedFDeriv ℝ j outputJointWave (0, v.2.2.2.2)‖ ≤ Wave j ∧
          ‖iteratedFDeriv ℝ j (mo p) (u, v.2.2.2.2)‖ ≤ O j * L ^ j) ∧
        (∀ u ζ j, ‖iteratedFDeriv ℝ j (fun t ↦ mo p (t, ζ)) u‖ ≤ O j * L ^ j) ∧
        (∀ backward low j k, IsComparablePair c C a₀ b₀ ρ low j k →
          ∀ r ∈ Icc 0 Δ, ∀ y,
          HasAmplitudeGrades D ρ (ρ ^ (-1 : ℝ)) L
            (orientedElapsedAmplitude backward b (endpointOutputMask f p output)
              (chartInputMask f p) (selectedEndpointMultiplier f p threshold) r)
            (mi p) (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y (Kglobal p)) ∧
        ∀ backward low j k, IsComparablePair c C a₀ b₀ ρ low j k → ∀ y,
          (∀ r, tsupport (FiniteChain.Graph.jointAmplitude ρ
            (orientedElapsedAmplitude backward b (endpointOutputMask f p output)
              (chartInputMask f p) (selectedEndpointMultiplier f p threshold) r)
            (mi p) (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y) ⊆ Kglobal p) ∧
          tsupport (fun v : V ↦ θ v.1 • jointElapsedAmplitude backward ρ b
            (endpointOutputMask f p output) (chartInputMask f p)
            (selectedEndpointMultiplier f p threshold) (mi p) (fun _ ↦ 0)
            (graphBranchCutoff low j) (outputCutoff k) 0 y v) ⊆ Kelapsed p := by
  classical
  obtain ⟨Kg, Ke, Qb, hKg, hKe, heq, hglobal, hcover, hQb, hnormalized⟩ :=
    exists_selected_normalizedResidual_profile f hρb hsrcρ c C a₀ b₀ ha₀ ra rb hra hab
      cost hcost A hA output ho hoc hout threshold hthreshold Δ θ hθ hθone
  have hzero p v (hv : v ∈ Kg p) : v.2.1 ≠ 0 := by
    rw [hglobal p] at hv
    have hn := hv.1.2.1.1
    change a₀ / (16 * annulusFactor c C) ≤ ‖v.2.1‖ at hn
    intro hz
    rw [hz, norm_zero] at hn
    have hf := two_le_annulusFactor c C
    have : 0 < a₀ / (16 * annulusFactor c C) := div_pos ha₀ (by linarith)
    linarith
  have hzeroe p v (hv : v ∈ Ke p) : v.2.2.1 ≠ 0 := by
    rw [heq p] at hv
    exact hzero p v.2 hv.2
  have hth : 1 ≤ threshold := f.radialThreshold_ge_one.trans hthreshold
  obtain ⟨Qt, Qs, Qg, hQt, hQs, hQg, hmasks⟩ :=
    exists_selected_elapsed_mask_profiles f threshold hth output ho hoc hout Ke hKe hzeroe
  obtain ⟨Qi, O, Wave, hQi, hO, hWave, hinput, houtput, hphysicalOutput, hwave⟩ :=
    exists_selected_elapsed_localizer_profiles f Ke hKe mi mo Ki Ii Ko Oo hi hmo
  obtain ⟨Bbase, hBbase, hphysicalGrade⟩ :=
    exists_selected_physicalResidual_profile f hρb hsrcρ ra rb hra hab cost hcost A hA
  obtain ⟨D, hD₁, hD₂, hD₃, hD₄, hD₅, hcomparable⟩ :=
    exists_selected_elapsed_comparable_profiles f threshold hth output ho hoc hout
      Δ c C a₀ b₀ ha₀ Kg hKg hzero mi mo Ki Ii Ko Oo hi hmo Qb hQb
  obtain ⟨Kg', Ke', _, _, _, heq', hglobal', hsupport⟩ :=
    exists_selected_elapsed_comparable_carriers (q := d+1) f output ho hoc hout
      threshold c C a₀ b₀ ha₀ θ hθ
  have heKg : Kg' = Kg := funext (fun p ↦ (hglobal' p).trans (hglobal p).symm)
  have heKe : Ke' = Ke := by
    funext p
    rw [heq' p, heKg, ← heq p]
  rw [heKg, heKe] at hsupport
  refine ⟨Kg, Ke, Qt, Qs, Qg, Qb, Qi, O, Wave, Bbase, D,
    hKg, hKe, heq, hglobal, hcover, hQt, hQs, hQg, hQb, hQi, hO, hWave, hBbase,
    hD₁, hD₂, hD₃, hD₄, hD₅, ?_⟩
  intro Rstar hRstar L ρ hL hρ Q B hQ hB Φ Cchart angular Fs W J
    hang hW hFs hphysical hbudget
  have hn := hnormalized Rstar hRstar L ρ hL hρ Q B hQ hB Φ Cchart angular
    hang hW hFs hphysical hbudget
  have hp := hphysicalGrade Rstar hRstar L hL Q B hQ hB Φ Cchart angular hW hphysical hbudget
  let b := fun p ↦ directRetardedAmplitudes
    (fun y i ↦ chartOutputMask f p y • (coefficient (f.chart p).index Q y i).map Complex.ofReal)
    (fun y ↦ chartOutputMask f p y • (zeroth (f.chart p).index B y).map Complex.ofReal)
    (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) 0)
    (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) 1) true
  have hc := hcomparable L ρ hL hρ b (fun p ↦ (hn p).1) (fun p ↦ (hn p).2.2.1)
  intro p Aoriginal Boriginal Ac Bc bp
  refine ⟨(hn p).1, (hn p).2.1, (hn p).2.2.1, hp p, ?_, ?_,
    hphysicalOutput L hL p, hc p, ?_⟩
  · intro u y v hv j
    have hm := hmasks L ρ hL hρ p v hv.1 j
    exact ⟨hm.1, hm.2.1, hm.2.2, (hn p).2.1 v hv.1 j, hinput L hL p y v j⟩
  · intro u y v hv j
    exact ⟨hwave p v hv.1 j, houtput L hL p u v.2.2.2.2 j⟩
  · intro backward low j k hpair y
    exact hsupport p (mi p) (fun _ ↦ 0) univ (hAnn p) bp backward ρ hρ low j k hpair 0 y

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
