module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.Regularizations
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

/-!
# Smooth retained residual amplitudes and measurable common regularizations

The third retained conic amplitude is the full physical derivative on the
actual common output plateau. It is therefore a globally smooth auxiliary
amplitude for the SAME common-masked operator, even when the original
coefficients are smooth only on their original domain. The compact-frequency
test formulas from `exists_selected_common_graph_regularizations` suffice to
prove measurability of both literal orientations on every datum.
Source: `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteResidual.SelectedChart RegularSector.FinitePdo
open Characteristic Characteristic.AmplitudeBounds Characteristic.ResidualCoordinates
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open Characteristic.UniformEvolution Characteristic.EvolutionIntegral.KernelIdentification
open FourierIntegral FourierIntegral.LowBounds.FrequencyCutoff
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "H" => SpacetimeL2 d (d+1)

/-- The smooth third retained amplitude agrees with the full physical `PW₁`
after applying the actual common masks. This smooth representative is used
by `selected_common_smooth_direct_residual` to construct the direct auxiliary
form required by `CompleteFactor`; the original coefficients and zeroth-order
term are preserved. The smoothness and column identity are exact
outputs of `exists_finite_direct_operator_bounds`
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selected_common_auxiliary_amplitudes
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (output : E → ℝ) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat) (W : Fin 3 → T → CMat)
    (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hphysical : ∀ v : T, (f.chart p).timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) →
      ∀ j : Fin (d+1), (fun k ↦ W 2 v k j) =
        WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
          (fun y k ↦ W 1 (physicalSlice (coordinateSplit (f.chart p).index) v.2.1 v.2.2.2 y) k j)
          ((coordinateSplit (f.chart p).index).symm (v.1, v.2.2.1))) :
    let b := fun k : Bool ↦ if k then curryCharacteristicMatrix (W 2)
      else curryCharacteristicMatrix (W 0) + curryCharacteristicMatrix (W 1)
    let original := directRetardedAmplitudes
      (fun y i ↦ (coefficient (f.chart p).index Q y i).map Complex.ofReal)
      (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal)
      (curryCharacteristicMatrix (W 0)) (curryCharacteristicMatrix (W 1))
    (∀ k, ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude (b k))) ∧
      ∀ k (β : E → ℂ) r,
        elapsedAmplitude (b k) (endpointOutputMask f p output) (chartInputMask f p) β r =
          elapsedAmplitude (original k) (endpointOutputMask f p output) (chartInputMask f p) β r := by
  intro b original
  have htime := (selected_output_retained_geometry f p hρb hsrcρ).2.2
  have hpw := retained_residual_eq_twoTimePhysicalApply (f.chart p).index Q B (W 1) (W 2)
    (f.chart p).timeMask (hW 1) hphysical
  refine ⟨?_, ?_⟩
  · intro k
    cases k
    · exact ((hW 0).comp evolutionToCharacteristicPoint.contDiff).add
        ((hW 1).comp evolutionToCharacteristicPoint.contDiff)
    · exact (hW 2).comp evolutionToCharacteristicPoint.contDiff
  · intro k β r
    cases k
    · rfl
    · funext y z ξ
      by_cases hy : endpointOutputMask f p output y = 0
      · simp [elapsedAmplitude, hy]
      · have ht := htime y (endpointOutputMask_tsupport_subset_chartOutputMask f p output hout
          (subset_tsupport _ hy))
        change (_ : ℂ) • W 2 _ = _ • twoTimePhysicalApply _ _ _ _ _ _ _
        rw [hpw y ht]

/-- The actual common-mask forward and literal-adjoint regularizations are
measurable for every datum. The realization hypotheses are precisely the
outputs of `exists_selected_common_graph_regularizations`; no new operator,
operator continuity, or differentiated-kernel estimate is assumed. Smoothness
of `G` and `W` and the physical column identity are retained construction outputs.
Consumer: `hm` and `hmAdj` in `CompleteFactor`
(`app:ch_regular:eq:chain-tail`, `app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selected_common_regularizations_aestronglyMeasurable
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (threshold : ℝ) (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat) (W : Fin 3 → T → CMat)
    (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hphysical : ∀ v : T, (f.chart p).timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) →
      ∀ j : Fin (d+1), (fun k ↦ W 2 v k j) =
        WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
          (fun y k ↦ W 1 (physicalSlice (coordinateSplit (f.chart p).index) v.2.1 v.2.2.2 y) k j)
          ((coordinateSplit (f.chart p).index).symm (v.1, v.2.2.1)))
    (G : T → ℝ) (hG : ContDiff ℝ ∞ G) :
    let Ψ : TwoTimePhase d := fun t s y η ↦ G (t, (s, (y, η)))
    let β := selectedEndpointMultiplier f p threshold
    let original := directRetardedAmplitudes
      (fun y i ↦ (coefficient (f.chart p).index Q y i).map Complex.ofReal)
      (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal)
      (curryCharacteristicMatrix (W 0)) (curryCharacteristicMatrix (W 1))
    ∀ Δ : ℝ, ∀ Treg : Bool → ℕ → ℝ → H →L[ℂ] H,
    (∀ k j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d+1) (d+1),
      Treg k j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (complexPhysicalCutoff j)
          (elapsedAmplitude (original k) (endpointOutputMask f p output) (chartInputMask f p) β r)) u) →
    (∀ k j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d+1) (d+1),
      (Treg k j r).adjoint (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
            (fun x y ξ ↦ (elapsedAmplitude (original k) (endpointOutputMask f p output)
              (chartInputMask f p) β r x y ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) y)) →
    ∀ k j u, AEStronglyMeasurable (fun r ↦ Treg k j r u) (volume.restrict (Icc 0 Δ)) ∧
      AEStronglyMeasurable (fun r ↦ (Treg k j r).adjoint u) (volume.restrict (Icc 0 Δ)) := by
  intro Ψ β original Δ Treg hreal hrealAdj k j u
  let b := fun k : Bool ↦ if k then curryCharacteristicMatrix (W 2)
    else curryCharacteristicMatrix (W 0) + curryCharacteristicMatrix (W 1)
  obtain ⟨hb, he⟩ := selected_common_auxiliary_amplitudes f p hρb hsrcρ output hout Q B W hW hphysical
  have hΨ : Continuous (fun v : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ v.1.1 v.1.2 v.2.1 v.2.2) := hG.continuous.comp
    (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hbc : Continuous (fun v : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b k v.1.1 v.1.2 v.2.1 v.2.2) := (hb k).continuous.comp
    ((continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd.fst)).prodMk
      continuous_snd.snd)
  obtain ⟨hχout, hχoutc, _⟩ := endpointOutputMask_properties f p ho hoc hout
  obtain ⟨_, hχsource, _, hχsourcec, _⟩ := chartPhysicalMasks_properties f p
  have hβ := (selectedEndpointMultiplier_bounds f p threshold).1.continuous
  have hr : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d+1) (d+1),
      Treg k j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (complexPhysicalCutoff j)
          (elapsedAmplitude (b k) (endpointOutputMask f p output) (chartInputMask f p) β r)) u := by
    intro j r hr u
    rw [he k β r]
    exact hreal k j r hr u
  have hra : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d+1) (d+1),
      (Treg k j r).adjoint (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
            (fun x y ξ ↦ (elapsedAmplitude (b k) (endpointOutputMask f p output)
              (chartInputMask f p) β r x y ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) y) := by
    intro j r hr u
    rw [he k β r]
    exact hrealAdj k j r hr u
  exact ⟨aestronglyMeasurable_elapsed_regularization Ψ (b k) _ _ _ hΨ hbc hχout.continuous
      hχsource.continuous hβ hχoutc hχsourcec complexPhysicalCutoff
      (fun j ↦ (complexPhysicalCutoff_contDiff j).continuous) complexPhysicalCutoff_hasCompactSupport
      Δ (Treg k) hr j u,
    aestronglyMeasurable_elapsed_adjoint_regularization Ψ (b k) _ _ _ hΨ hbc hχout.continuous
      hχsource.continuous hβ hχoutc hχsourcec complexPhysicalCutoff
      (fun j ↦ (complexPhysicalCutoff_contDiff j).continuous) complexPhysicalCutoff_hasCompactSupport
      Δ (Treg k) hra j u⟩

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
