module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.NormalizedWordObservation
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.ObservationRestriction
public import JanetCartan.Analysis.Microlocal.NormalizedResidualWords.MeasuredDecay

/-!
# From complex word observations to the original real residual powers

Apply the exact observation and support identities to the same measured words,
then use the published finite-sum theorem on the actual normalized residual.
The original domain, source cutoff, external halves, full B and single source
identity subtraction remain fixed (`app:ch_regular:eq:resolved-angular-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
open Set MeasureTheory
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly RegularSector.Realization
open RegularSector.NormalizedSolver RegularSector.NormalizedResidualWords
open RegularSector.FiniteMasks.ActualFamily RegularSector.FiniteResidual.FiniteIdentity
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.RetardedLocalization
open LocalSobolev ResidualLocalization FourierIntegral.LowBounds
variable {d : ℕ} {ι : Type*}
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
variable (L : ι → ℝ) (Q : ι → Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
variable (B : ι → Euclidean (d+1) → MetricTensor (d+1))
variable (W₁ : ι → f.centers → TwoTimeAmplitude d (d+1))
variable (output : Euclidean (d+1) → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
variable (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : ι → f.centers → (SpacetimeL2 d (d+1)) →L[ℂ] (SpacetimeL2 d (d+1)))
variable (μ ν : Euclidean (d+1) → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
variable (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
variable {U : Set (Euclidean (d+1))} (hU : MeasurableSet U)
variable (hμU : tsupport μ ⊆ U) (hνU : tsupport ν ⊆ U)
variable (W : Set (Euclidean (d+1))) (hW : MeasurableSet W) (s : ℕ) (ρ A : ι → ℝ)
variable (u : ι → LocalL2 U (EuclideanSpace ℝ (Fin (d+1))))
include hμU hνU

/-- Transfer the proved complex observation of a complete selected word to
the original real restriction space. The analytic producer is
`normalizedSource_alternatingChain_observation_rapidDecayAt`; support transport
and real projection are proved here, after the entire word
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:resolved-angular-tail`). -/
theorem normalizedSource_selectedWord_rapidDecayAt_of_global
    (w : List (((f.centers × Fin 3) ⊕ Unit) × Bool)) :
    let P : ι → (((f.centers × Fin 3) ⊕ Unit) × Bool) → (SpacetimeL2 d (d+1)) →L[ℂ] (SpacetimeL2 d (d+1)) := fun i a ↦
      measuredOperator μ ν hμ hν hμb hνb
        (selectedFullPhysicalResidualTerm f hK (L i) (Q i) (B i) (W₁ i)
          output ho hob hib (T i) a)
    let J := fun i a ↦ localRetardedOperator hU U (P i a)
    let D := fun i ↦ pairedSource f hK (L i) output ho hob-1
    RapidDecayAt (restrictionSobolevScale univ (EuclideanSpace ℂ (Fin (d+1))) MeasurableSet.univ) s ρ A
      (fun i ↦ restrictL2 univ (D i ((w.map (P i)).prod
        (l2ComplexInclusion volume (SmallSupport.zeroExtend hU (u i)))))) →
    RapidDecayAt (restrictionSobolevScale W (EuclideanSpace ℝ (Fin (d+1))) hW) s ρ A (fun i ↦
      localRealCompression hU W (D i) (l2RealPart (volume.restrict U)
        ((w.map (J i)).prod (l2ComplexInclusion (volume.restrict U) (u i))))) := by
  intro P J D hword
  have h := realPart_restrictL2_rapidDecayAt_of_univ ρ A
    (fun i ↦ D i ((w.map (P i)).prod
      (l2ComplexInclusion volume (SmallSupport.zeroExtend hU (u i))))) s W hW hword
  convert h using 1
  funext i
  exact normalizedSource_selectedWord_observation_eq f hK (L i) (Q i) (B i) (W₁ i)
    output ho hob hib (T i) μ ν hμ hν hμb hνb hU hμU hνU W w (u i)

/-- Apply the published measured-word summation to the actual normalized
residual. The whole-space complex word estimates are transported above; the
conclusion is the exact real local power observation required by
`rapidDecayAt_inverse_of_finite_chains.hchain`. This is a deduction from the
individual word estimates, not their actual initialized construction
(`app:ch_regular:eq:finite-observation`, `app:ch_regular:eq:resolved-angular-tail`). -/
theorem normalizedSource_measuredResidual_hchain_of_complex_words
    (hsupp : tsupport output ⊆ Metric.ball x f.physicalRadius)
    (R C : ι → f.centers → ℝ)
    (hb : ∀ i p, FourierIntegral.GraphNormalAmplitudeBounds
      (RegularSector.Characteristic.PdoRealization.maskedPhysicalPDOCycleSymbol
        (FiniteAlgebraic.chartOutputMask f p) (FiniteAlgebraic.chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L i) (Q i) (B i) 1)) (R i p) (C i p))
    (hword : ∀ j (w : Fin j → (((f.centers × Fin 3) ⊕ Unit) × Bool)),
      RapidDecayAt (restrictionSobolevScale univ (EuclideanSpace ℂ (Fin (d+1))) MeasurableSet.univ) s ρ A
        (fun i ↦ restrictL2 univ ((fun i ↦ pairedSource f hK (L i) output ho hob-1) i
          ((List.ofFn (fun k ↦ (fun i a ↦ measuredOperator μ ν hμ hν hμb hνb (selectedFullPhysicalResidualTerm f hK (L i) (Q i) (B i) (W₁ i) output ho hob hib (T i) a)) i (w k))).prod
            (l2ComplexInclusion volume (SmallSupport.zeroExtend hU (u i))))))) :
    let retarded := fun i ↦ (sourceCutMultiplier output ho hob).comp
      ((FiniteEvolution.finitePhysicalOperator (fun p ↦ (f.chart p).index) (T i)).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
    let P := fun i ↦ measuredOperator μ ν hμ hν hμb hνb
      (pairedResidual f hK (L i) (Q i) (B i) output ho hob (W₁ i) (retarded i))
    ∀ j, RapidDecayAt (restrictionSobolevScale W (EuclideanSpace ℝ (Fin (d+1))) hW) s ρ A (fun i ↦
      localRealCompression hU W ((fun i ↦ pairedSource f hK (L i) output ho hob-1) i)
        ((localRealCompression hU U (P i)^j) (u i))) := by
  intro retarded P
  apply measured_realResidual_hchain_of_words f hK output ho hob hib hsupp L Q B W₁ T R C hb
    μ ν hμ hν hμb hνb hU (restrictionSobolevScale W (EuclideanSpace ℝ (Fin (d+1))) hW) s ρ A
    (fun i ↦ (localRealCompression hU W ((fun i ↦ pairedSource f hK (L i) output ho hob-1) i)).toLinearMap) u
  intro j w
  have h := normalizedSource_selectedWord_rapidDecayAt_of_global f hK L Q B W₁ output ho hob hib T
    μ ν hμ hν hμb hνb hU hμU hνU W hW s ρ A u (List.ofFn w)
    (by simpa only [List.map_ofFn, Function.comp_def] using hword j w)
  simpa only [List.map_ofFn, Function.comp_def, ContinuousLinearMap.coe_coe] using h

end JanetCartan.ArbitraryAccuracy.SelectedLocalization

