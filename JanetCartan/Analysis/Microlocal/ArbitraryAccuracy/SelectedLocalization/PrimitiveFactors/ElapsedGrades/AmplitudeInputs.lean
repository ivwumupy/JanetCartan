module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.ResidualProfiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.PhaseCarriers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.PhysicalAmplitude
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Comparable
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.ResidualCarriers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OutputJets

/-!
# Common amplitude profiles for the chartwise elapsed cutoffs

A single compact majorant carrier gives uniform profiles for every chart's
own retarded time slab. The actual carrier is then restricted to that chart's
buffered elapsed cutoff, exactly as required by the phase construction.
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

/-- Uniform elapsed amplitude inputs for all original chart slabs on the same
carriers used by `exists_selected_elapsed_phase_inputs`. A compact majorant
cutoff is constructed solely for estimating the primitive jets, and every
conclusion uses the actual chartwise cutoff. This instantiates the normalized
residual, masks, physical grades, comparable grades and both support statements;
no analytic profile is left as a premise. The remaining inputs are the original
coefficient profiles, retained construction certificates and protected localizers
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_selected_elapsed_amplitude_inputs
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
    (mi mo : f.centers → LocalizerSymbol (d+1))
    (Ki Ii Ko Oo : f.centers → Set (E × E))
    (hi : ∀ p, IsBufferedLocalizer (mi p) (Ki p) (Ii p))
    (hmo : ∀ p, IsBufferedLocalizer (mo p) (Ko p) (Oo p))
    (hAnn : ∀ p, tsupport (mi p) ⊆ univ ×ˢ frequencyAnnulus a₀ b₀) :
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
          ∀ r ∈ Icc 0 (Δ p), ∀ y,
          HasAmplitudeGrades D ρ (ρ ^ (-1 : ℝ)) L
            (orientedElapsedAmplitude backward b (endpointOutputMask f p output)
              (chartInputMask f p) (selectedEndpointMultiplier f p threshold) r)
            (mi p) (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y (Kglobal p)) ∧
        ∀ backward low j k, IsComparablePair c C a₀ b₀ ρ low j k → ∀ y,
          (∀ r, tsupport (FiniteChain.Graph.jointAmplitude ρ
            (orientedElapsedAmplitude backward b (endpointOutputMask f p output)
              (chartInputMask f p) (selectedEndpointMultiplier f p threshold) r)
            (mi p) (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y) ⊆ Kglobal p) ∧
          tsupport (fun v : V ↦ θ p v.1 • jointElapsedAmplitude backward ρ b
            (endpointOutputMask f p output) (chartInputMask f p)
            (selectedEndpointMultiplier f p threshold) (mi p) (fun _ ↦ 0)
            (graphBranchCutoff low j) (outputCutoff k) 0 y v) ⊆ Kelapsed p := by
  classical
  let upper : ℝ := ∑ p, max (Δ p) 0
  have hupper p : Δ p ≤ upper := (le_max_left _ _).trans
    (Finset.single_le_sum (fun p _ ↦ le_max_right (Δ p) 0) (Finset.mem_univ p))
  let Ktime : Set ℝ := (⋃ p, tsupport (θ p)) ∪ Icc 0 upper
  have hKt : IsCompact Ktime := (isCompact_iUnion hθ).union isCompact_Icc
  obtain ⟨χ, hsχ, _, hcχ, _, hplateau⟩ := CompatibleResponse.exists_compact_family_cutoff
    hKt isOpen_univ (subset_univ _)
  let θwide := fun r ↦ (χ r : ℂ)
  have hone r (hr : r ∈ Ktime) : θwide r = 1 := by
    have hh : r ∈ {r | χ r = 1} := interior_subset (hplateau hr)
    change χ r = 1 at hh
    simp only [θwide, hh, Complex.ofReal_one]
  have hwide : HasCompactSupport θwide := hcχ.comp_left Complex.ofReal_zero
  have hcoverTime p : tsupport (θ p) ⊆ tsupport θwide := by
    intro r hr
    exact subset_tsupport _ (by change θwide r ≠ 0; rw [hone r (Or.inl (mem_iUnion.mpr ⟨p, hr⟩))]; exact one_ne_zero)
  obtain ⟨Kg, Ke, Qt, Qs, Qg, Qb, Qi, O, Wave, Bbase, D,
    hKg, hKe, heq, hglobal, _, hQt, hQs, hQg, hQb, hQi, hO, hWave, hBbase,
    hD₁, hD₂, hD₃, hD₄, hD₅, hgrades⟩ :=
    exists_selected_completeFactor_amplitude_inputs f hρb hsrcρ c C a₀ b₀ ha₀ ra rb hra hab
      cost hcost A hA output ho hoc hout threshold hthreshold upper θwide hwide
      (fun r hr ↦ hone r (Or.inr hr)) mi mo Ki Ii Ko Oo hi hmo hAnn
  let Ksmall := fun p ↦ tsupport (θ p) ×ˢ Kg p
  have hsmall p : Ksmall p ⊆ Ke p := by
    intro v hv
    rw [heq p]
    exact ⟨hcoverTime p hv.1, hv.2⟩
  have hjet p u y : elapsedOutputJetCarrier (Ksmall p) (mi p) (mo p) u y ⊆
      elapsedOutputJetCarrier (Ke p) (mi p) (mo p) u y :=
    fun _ hv ↦ ⟨hsmall p hv.1, hv.2⟩
  have hcover p : Icc 0 (Δ p) ×ˢ Kg p ⊆ Ksmall p := by
    rintro ⟨r, v⟩ ⟨hr, hv⟩
    exact ⟨subset_tsupport _ (by change θ p r ≠ 0; rw [hθone p r hr]; exact one_ne_zero), hv⟩
  refine ⟨Kg, Ksmall, Qt, Qs, Qg, Qb, Qi, O, Wave, Bbase, D,
    hKg, fun p ↦ (hθ p).prod (hKg p), fun _ ↦ rfl, hglobal, hcover,
    hQt, hQs, hQg, hQb, hQi, hO, hWave, hBbase, hD₁, hD₂, hD₃, hD₄, hD₅, ?_⟩
  intro Rstar hRstar L ρ hL hρ Q B hQ hB Φ Cchart angular Fs W J
    hang hW hFs hphysical hbudget p Aoriginal Boriginal Ac Bc b
  have hb := hgrades Rstar hRstar L ρ hL hρ Q B hQ hB Φ Cchart angular
    hang hW hFs hphysical hbudget p
  rcases hb with ⟨hs, hn, ht, hp, hm, hw, ho', hg, _⟩
  refine ⟨hs, fun v hv j ↦ hn v (hsmall p hv) j,
    fun r hr v hv j ↦ ht r ⟨hr.1, hr.2.trans (hupper p)⟩ v hv j, hp,
    fun u y v hv j ↦ hm u y v (hjet p u y hv) j,
    fun u y v hv j ↦ hw u y v (hjet p u y hv) j, ho', ?_, ?_⟩
  · intro backward low j k hpair r hr y
    exact hg backward low j k hpair r ⟨hr.1, hr.2.trans (hupper p)⟩ y
  · obtain ⟨Kg', Ke', _, _, _, heq', hglobal', hsupport⟩ :=
      exists_selected_elapsed_comparable_carriers (q := d+1) f output ho hoc hout
        threshold c C a₀ b₀ ha₀ (θ p) (hθ p)
    have heKg : Kg' = Kg := funext (fun a ↦ (hglobal' a).trans (hglobal a).symm)
    have heKe : Ke' p = Ksmall p := by rw [heq' p, heKg]
    intro backward low j k hpair y
    have hh := hsupport p (mi p) (fun _ ↦ 0) univ (hAnn p) b backward ρ hρ low j k hpair 0 y
    rwa [heKg, heKe] at hh

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
