module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.PhysicalGraphRealizations
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Regularizations.Chart
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.Amplitudes
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Estimates
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SupportedGraphRealizations

/-!
# Graph realizations of the original selected physical factors

Apply the existing collared-matrix regularization construction to the actual
selected amplitudes and common physical masks. Compact smoothness of those
same buffered matrices supplies the auxiliary graph bounds; no new symbol
band comparison is needed for this existence input. The envelope's uniform
constants still come from its separately proved quantitative history profiles.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
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

/-- The actual selected matrices have both compact-frequency graph
realizations, their literal adjoints and both strong limits, with the original
physical masks and cutoff at `2*threshold`. The inputs are the same-witness
smoothness, support and phase outputs of `ProtectedConstruction.FullSource`.
The auxiliary bound may vary with the coefficient field, as allowed by the
existing `Creg : I → ℝ` in the full-source envelope theorem. This existence
input requires no additional radial-band comparison and asserts no uniform
history envelope by itself (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_selected_physical_graph_realizations
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius)
    (threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (angular : Euclidean d → ℝ) (hang : ContDiff ℝ ∞ angular)
    (hplateau : ∀ ξ ∈ tsupport (selectedEndpointMultiplier f p threshold),
      conicMask angular =ᶠ[𝓝 (spatialPart ξ)] (fun _ ↦ 1)) :
    let c := f.chart p
    let z : Z := ((coordinateSplit c.index x).1,
      ((coordinateSplit c.index x).2, (coordinateSplit c.index p.val.val).2))
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
      CappedGraphRealizations (3*c.maskRadius/4) (curriedPhase c.radialSection C)
        (if o = 0 then W 0 + W 1 else W 2)
        (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointMultiplier f p threshold) (Creg o) := by
  intro c z Q B h Φ C hbuffer hsmooth hdiff hnear hphase hsourceTime Fs W hFs hWs hsupport
  obtain ⟨hout,hcout,_⟩ := endpointOutputMask_properties f p ho hoc hos
  obtain ⟨_,hs,_,hcs,_⟩ := chartPhysicalMasks_properties f p
  obtain ⟨hbox,hslab,_⟩ := common_output_retained_geometry f p hρb hsrcρ output hos
  obtain ⟨aperture,hAp,hcar⟩ := exists_chart_temporal_aperture c hρb hsrcρ
    (f.angularMask p) (f.angularMask_support p)
  let β : E → ℂ := fun ξ ↦ dilatedConicMask (f.angularMask p) (2*threshold) (physicalCoordinates c.index ξ)
  have hβsub : tsupport β ⊆ retainedFrequencyDomain c.radialSection z
      (retainedRadius c.targetRadius c.bufferRadius) aperture (1/2) := by
    intro ξ hξ
    have hcan := PhysicalCutoff.tsupport_complex_physical_dilatedConicMask_subset
      (f.angularMask p) c.index (zero_lt_one.trans_le hthreshold) hξ
    have hr : ξ ∈ tsupport (dilatedConicMask (f.angularMask p ∘ physicalCoordinates c.index) threshold) :=
      tsupport_comp_subset Complex.ofReal_zero _ hcan
    refine ⟨dilatedConicMask_tsupport_subset_fullAngularCone c.radialSection z _ _ _ hcar
      (zero_lt_one.trans_le hthreshold) hr, ?_⟩
    have he := (hplateau ξ hξ).eq_of_nhds
    have hn : conicMask angular (spatialPart ξ) ≠ 0 := by rw [he]; norm_num
    have hn' := (conicMask_tsupport_subset angular (subset_tsupport _ hn)).1
    change (1/2 : ℝ) < ‖spatialPart ξ‖
    linarith
  obtain ⟨Rs,hRs⟩ := hcs.exists_bound_of_continuousOn (f := fun y : E ↦ y) continuous_id.continuousOn
  let Rbox := 1 + |z.1| + ‖z.2.1‖ + retainedRadius c.targetRadius c.bufferRadius + |Rs|
  have hε := (retainedRadius_bounds c.targetRadius_pos c.bufferRadius_pos).1
  have hRbox : 0 < Rbox := by dsimp only [Rbox]; positivity
  have hX : ∀ y ∈ elapsedPhysicalBox z (retainedRadius c.targetRadius c.bufferRadius/2), ‖y‖ ≤ Rbox := by
    intro y hy
    have hn := norm_le_on_elapsedPhysicalBox hy
    dsimp only [Rbox]
    linarith [abs_nonneg Rs]
  have hY : ∀ y ∈ tsupport (chartInputMask f p), ∀ i : Fin (d+1), |y i| ≤ Rbox := by
    intro y hy i
    have hn := (PiLp.norm_apply_le y i).trans (hRs y hy)
    rw [Real.norm_eq_abs] at hn
    dsimp only [Rbox]
    linarith [le_abs_self Rs,abs_nonneg z.1,norm_nonneg z.2.1]
  obtain ⟨D,Treg,hlow,hbound,hreal,hrealAdj,hlim,hlimAdj,_⟩ :=
    exists_retained_collared_graph_regularizations c.radialSection z c.targetRadius_pos
      c.bufferRadius_pos c.maskRadius_pos hρb hsrcρ hAp
      (endpointOutputMask f p output) (chartInputMask f p) hout hs hcout hcs
      hbox (fun y hy ↦ hslab y (subset_tsupport _ hy)) Rbox hRbox hX hY
      c.index (f.angularMask p) (f.angularMask_smooth p) hcar threshold hthreshold hβsub
      (closedBall x RQ) Q c.phaseCost h Φ C hbuffer hsmooth hdiff hnear hphase hsourceTime
      angular hang Fs hFs hWs hsupport
  have hgraph (k : Bool) : CappedGraphRealizations (3*c.maskRadius/4) (curriedPhase c.radialSection C)
      (if k then W 2 else W 0 + W 1) (endpointOutputMask f p output) (chartInputMask f p) β (D k) := by
    refine ⟨complexPhysicalCutoff,complexPhysicalCutoff_contDiff,
      complexPhysicalCutoff_hasCompactSupport,Treg k,?_,hbound k,?_,?_,fun _ _ ↦ rfl,?_,?_⟩
    · simpa [W,Fs,c,β,selectedConicAmplitude,selectedEndpointMultiplier] using hlow k
    · simpa [W,Fs,c,β,selectedConicAmplitude,selectedEndpointMultiplier] using hreal k
    · simpa [W,Fs,c,β,selectedConicAmplitude,selectedEndpointMultiplier] using hrealAdj k
    · simpa [W,Fs,c,β,selectedConicAmplitude,selectedEndpointMultiplier] using hlim k
    · simpa [W,Fs,c,β,selectedConicAmplitude,selectedEndpointMultiplier] using hlimAdj k
  refine ⟨fun o ↦ if o = 0 then D false else D true,?_⟩
  intro o
  have hβeq : selectedEndpointMultiplier f p threshold = β := by
    funext ξ
    rfl
  rw [hβeq]
  by_cases ho : o = 0
  · simpa only [ite_eq_left ho,Bool.false_eq_true,↓reduceIte] using hgraph false
  · simpa only [ite_eq_right ho,↓reduceIte] using hgraph true

end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
