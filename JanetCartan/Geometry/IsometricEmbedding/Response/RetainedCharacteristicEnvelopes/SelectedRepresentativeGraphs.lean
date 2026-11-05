module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.SelectedGraphRealizations
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CommonPhysicalMasks
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CappedKernels

/-!
# The selected graph certificates on the same controlled phase

The actual common masks and frequency carrier put the entire elapsed interval
inside the selected representative's plateau. Transfer the graph realizations,
regularizations and both literal adjoint limits without changing the operator.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
open RetainedFactors
open RegularSector.Characteristic ConicPhase UniformEvolution EvolutionIntegral ResidualCoordinates
open ConicAmplitude AmplitudeBounds SymbolBudgets FourierIntegral LowBounds FrequencyCutoff
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteEvolution RegularSector.FiniteAlgebraic RegularSector.FinitePdo
open RegularSector.FiniteAssembly RegularSector.FiniteResidual.SelectedChart
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
  {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)

/-- Instantiate the graph-realization input of the full-source envelope on
the original selected matrices and common physical masks. The original source
buffer, output containment and multiplier carrier prove the representative
agreement over the entire interval, including its literal adjoint. No graph
realization or derivative envelope is a premise. The SAME auxiliary constants
and regularizations from the collared-matrix producer are retained
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_selected_physical_representative_graph_realizations
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    {ε aperture : ℝ} (hε : 0 < ε) (hsrc : (f.chart p).maskRadius ≤ ε)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius)
    (threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (angular : Euclidean d → ℝ) (hang : ContDiff ℝ ∞ angular)
    (hplateau : ∀ ξ ∈ tsupport (selectedEndpointMultiplier f p threshold),
      conicMask angular =ᶠ[𝓝 (spatialPart ξ)] (fun _ ↦ 1)) :
    let c := f.chart p
    let z : Z := ((coordinateSplit c.index x).1,
      ((coordinateSplit c.index x).2, (coordinateSplit c.index p.val.val).2))
    MapsTo (CompatibleResponse.primaryCoordinateChange c.index)
      (tsupport f.inputMask ∪ tsupport f.outputMask) (elapsedPhysicalBox z (ε/2)) →
    tsupport (selectedEndpointMultiplier f p threshold) ⊆
      retainedFrequencyDomain c.radialSection z ε aperture (1/2) →
    ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1/2 →
    ∀ χg : TC → ℝ, (∀ q ∈ closedBall (z.1,z) (4*ε), χg =ᶠ[𝓝 q] (fun _ ↦ 1)) →
    ∀ (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
      (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph TC TC),
    closedBall (z.1, z) c.targetRadius ⊆ C.target →
    ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
    (∀ v ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C v) v) →
    (∀ v ∈ closedBall (z.1, z) c.targetRadius, ‖twoTimePhaseMixed C v - 1‖ ≤ 1/2) →
    (∀ j, cNorm (closedBall (z.1, z) c.targetRadius) j (twoTimePhase C) ≤
      c.phaseCost j * (1 + cNorm (closedBall x RQ) (j+1) Q)) →
    (∀ v ∈ C.target, (C.symm v).2.1 = v.2.1) →
    let Fs := selectedBufferedAmplitude f p Q B Φ C
    let W := selectedConicAmplitude f p Q B Φ C angular
    (∀ k : Fin 3, ContDiff ℝ ∞ (Fs k)) →
    (∀ k : Fin 3, ContDiff ℝ ∞ (collared c.radialSection (if k = 0 then 0 else 1) angular (Fs k))) →
    (∀ k : Fin 3, tsupport (collared c.radialSection (if k = 0 then 0 else 1) angular (Fs k)) ⊆
      ConicPhase.domain c.radialSection (C.target ∩ C.symm ⁻¹'
        (ball z.1 (c.maskRadius/2) ×ˢ (ball z.1 (c.maskRadius/2) ×ˢ ball z.2 (c.maskRadius/2))))) →
    ∃ Creg : Fin 2 → ℝ, ∀ o : Fin 2,
      CappedGraphRealizations (3*c.maskRadius/4)
        (SmoothRepresentative.curriedRepresentative c.radialSection δ hδ χg (twoTimePhase C))
        (if o = 0 then W 0 + W 1 else W 2)
        (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointMultiplier f p threshold) (Creg o) := by
  intro c z hbox hβ δ hδ hδhalf χg heg Q B h Φ C hbuffer hsmooth hdiff hnear hphase hsourceTime
    Fs W hFs hWs hsupport
  obtain ⟨Creg,hgraph⟩ := exists_selected_physical_graph_realizations f p hρb hsrcρ
    output ho hoc hos threshold hthreshold angular hang hplateau
    Q B h Φ C hbuffer hsmooth hdiff hnear hphase hsourceTime hFs hWs hsupport
  have hout : tsupport (endpointOutputMask f p output) ⊆ elapsedPhysicalBox z (ε/2) :=
    subset_union_left.trans (selected_common_physical_masks_subset_stationary_box f p z ε hbox output hos)
  refine ⟨Creg,fun o ↦ (hgraph o).of_supported_phase_eq ?_⟩
  intro t ht y u ξ hA
  have ho' : endpointOutputMask f p output y ≠ 0 := fun he ↦ hA
    (elapsedAmplitude_eq_zero_of_mask _ _ _ _ _ _ _ _ (Or.inl he))
  have hβ' : selectedEndpointMultiplier f p threshold ξ ≠ 0 := fun he ↦ hA
    (elapsedAmplitude_eq_zero_of_mask _ _ _ _ _ _ _ _ (Or.inr (Or.inr he)))
  have hmem := capped_elapsedPoint_mem_phase_plateau c.radialSection z hε hsrc ht
    (hout (subset_tsupport _ ho')) (hβ (subset_tsupport _ hβ'))
  exact (SmoothRepresentative.elapsed_representative_eventuallyEq c.radialSection C
    hδ heg hmem (hδhalf.trans (hβ (subset_tsupport _ hβ')).2.le)).eq_of_nhds

end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
