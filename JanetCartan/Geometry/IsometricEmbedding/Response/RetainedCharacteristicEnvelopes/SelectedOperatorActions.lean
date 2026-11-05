module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.PhysicalGraphRealizations
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Regularizations.Chart
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.Amplitudes
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Estimates
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SupportedGraphRealizations
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Masks

/-!
# Integral actions of the original once-capped selected operators

The actual buffered matrices construct the common-mask retarded test action.
Density then identifies that action and its literal adjoint with the supplied
original operators. Both characteristic orders retain the original norm bound,
physical masks, doubled frequency collar and complete elapsed interval.
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
local notation "H" => SpacetimeL2 d (d+1)
open EvolutionIntegral.UncutTestAction

/-- Identify the actual once-capped selected operators with the full elapsed
integrals used by the characteristic envelope, including their literal
adjoints. The original compact buffered matrices construct the canonical
retarded test action; density identifies it with the supplied original Op.
No second operator is substituted and neither physical mask is applied twice.
Both W0+W1 and full PW1 keep their original doubled frequency collar
(`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selected_once_capped_operator_actions
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius)
    (hob : ∀ y, ‖output y‖ ≤ 1)
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
    ∀ G : TC → ℝ,
      (∀ q ∈ tsupport (collared c.radialSection 0 angular (Fs 0)) ∪
        tsupport (collared c.radialSection 1 angular (Fs 1)), G =ᶠ[𝓝 q] phase c.radialSection C) →
      (∀ q : TC, c.timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) →
        collared c.radialSection 1 angular (Fs 2) q ≠ 0 → G =ᶠ[𝓝 q] phase c.radialSection C) →
    ∀ (χout χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
      (base : Fin 2 → ℝ) (cost : Fin 2 → ℕ → ℝ) (Op : Fin 2 → H →L[ℂ] H),
    let Ψ := fun t s y ξ ↦ G (t,(s,(y,ξ)))
    let β := selectedEndpointMultiplier f p threshold
    (∀ o : Fin 2, RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*c.maskRadius/4)
      (z.1-c.maskRadius/2) Ψ (if o=0 then W 0+W 1 else W 2)
      χout χsource β hs o.val (base o) (cost o) (Op o)) →
    (∀ y, (output y : ℂ)*χout ((physicalCoordinates c.index).symm y) = (output y : ℂ)) →
    (∀ y, χsource ((physicalCoordinates c.index).symm y)*(f.inputMask y : ℂ) = (f.inputMask y : ℂ)) →
    let e := physicalCoordinates c.index
    let Mo := sourceCutMultiplier (r := d+1) (output ∘ e)
      (ho.continuous.comp e.continuous) (fun y ↦ hob (e y))
    let Mi := sourceCutMultiplier (r := d+1) (f.inputMask ∘ e)
      (f.inputMask_smooth.continuous.comp e.continuous) (fun y ↦ by
        simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (f.inputMask_range (e y)).1]
          using (f.inputMask_range (e y)).2)
    let capped := fun o ↦ Mo.comp ((Op o).comp Mi)
    (∀ o, ‖capped o‖ ≤ base o) ∧
    (∀ o u, capped o u = elapsedGraphIntegral (3*c.maskRadius/4) Ψ
      (if o=0 then W 0+W 1 else W 2) (endpointOutputMask f p output) (chartInputMask f p) β u) ∧
    (∀ o u, (capped o).adjoint u = ∫ t in Icc 0 (3*c.maskRadius/4),
      (elapsedGraph Ψ (if o=0 then W 0+W 1 else W 2)
        (endpointOutputMask f p output) (chartInputMask f p) β t).adjoint u) := by
  intro c z Q B h Φ C hbuffer hsmooth hdiff hnear hphase hsourceTime Fs W hFs hWs hsupport
    G hG hGres χout χsource hsLocal base cost Op Ψ βorig hOp hlocalout hlocalin e Mo Mi capped
  obtain ⟨hout,hcout,_⟩ := endpointOutputMask_properties f p ho hoc hos
  obtain ⟨_,hs,_,hcs,_⟩ := chartPhysicalMasks_properties f p
  obtain ⟨hbox,hslab,hcommonTime⟩ := common_output_retained_geometry f p hρb hsrcρ output hos
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
  obtain ⟨D,Treg,hlow,hbound,hreal,hrealAdj,hlim,hlimAdj,canonical,hcanonicalBound,hcanonicalIntegral,hcanonicalAdj,hcanonicalTest⟩ :=
    exists_retained_collared_graph_regularizations c.radialSection z c.targetRadius_pos
      c.bufferRadius_pos c.maskRadius_pos hρb hsrcρ hAp
      (endpointOutputMask f p output) (chartInputMask f p) hout hs hcout hcs
      hbox (fun y hy ↦ hslab y (subset_tsupport _ hy)) Rbox hRbox hX hY
      c.index (f.angularMask p) (f.angularMask_smooth p) hcar threshold hthreshold hβsub
      (closedBall x RQ) Q c.phaseCost h Φ C hbuffer hsmooth hdiff hnear hphase hsourceTime
      angular hang Fs hFs hWs hsupport
  have hβeq : βorig = β := rfl
  have htime : ∀ y, endpointOutputMask f p output y ≠ 0 →
      c.timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1) := by
    intro y hy
    exact hcommonTime y (subset_tsupport _ hy)
  have htestEq (o : Fin 2) (u : graphTestSpace (d+1) (d+1)) (y : E) :
      retardedPhysicalIntegral Ψ (if o=0 then W 0+W 1 else W 2)
        (endpointOutputMask f p output) (chartInputMask f p) β hs (z.1-c.maskRadius/2) u y =
      retardedPhysicalIntegral (curriedPhase c.radialSection C)
        (if o=0 then W 0+W 1 else W 2)
        (endpointOutputMask f p output) (chartInputMask f p) β hs (z.1-c.maskRadius/2) u y := by
    by_cases hzero : o=0
    · simp only [hzero,ite_true]
      exact solver_retardedPhysicalIntegral_eq_supported c.radialSection C
        (collared c.radialSection 0 angular (Fs 0)) (collared c.radialSection 1 angular (Fs 1))
        G hG _ _ _ hs _ u y
    · simp only [hzero,ite_false]
      exact residual_retardedPhysicalIntegral_eq_supported c.radialSection C
        (collared c.radialSection 1 angular (Fs 2)) G c.timeMask hGres _ _ _ htime hs _ u y
  have hgraphEq (o : Fin 2) (t : ℝ) :
      elapsedGraph Ψ (if o=0 then W 0+W 1 else W 2)
        (endpointOutputMask f p output) (chartInputMask f p) β t =
      elapsedGraph (curriedPhase c.radialSection C) (if o=0 then W 0+W 1 else W 2)
        (endpointOutputMask f p output) (chartInputMask f p) β t := by
    by_cases hzero : o=0
    · simp only [hzero,ite_true]
      exact solver_elapsedGraph_eq_supported c.radialSection C
        (collared c.radialSection 0 angular (Fs 0)) (collared c.radialSection 1 angular (Fs 1))
        G hG _ _ _ t
    · simp only [hzero,ite_false]
      exact residual_elapsedGraph_eq_supported c.radialSection C
        (collared c.radialSection 1 angular (Fs 2)) G c.timeMask hGres _ _ _ htime t
  let which : Fin 2 → Bool := fun o ↦ if o=0 then false else true
  have hcanonical (o : Fin 2) : capped o = canonical (which o) := by
    apply DFunLike.coe_injective
    apply denseRange_graphTestToLp.equalizer (capped o).continuous (canonical (which o)).continuous
    funext u
    apply Lp.ext
    have hret := retained_retarded_common_masks_test (closedBall x RQ) Q B
      (3*c.maskRadius/4) (z.1-c.maskRadius/2) Ψ (if o=0 then W 0+W 1 else W 2)
      χout χsource βorig hsLocal o.val (base o) (cost o) (Op o) (hOp o)
      (output ∘ e) (f.inputMask ∘ e) (ho.continuous.comp e.continuous)
      (f.inputMask_smooth.comp e.contDiff) (fun y ↦ hob (e y))
      (fun y ↦ by simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (f.inputMask_range (e y)).1]
        using (f.inputMask_range (e y)).2)
      (fun y ↦ by simpa only [Function.comp_apply,e,ContinuousLinearEquiv.symm_apply_apply] using hlocalout (e y))
      (fun y ↦ by simpa only [Function.comp_apply,e,ContinuousLinearEquiv.symm_apply_apply] using hlocalin (e y)) u
    have hcan := hcanonicalTest (which o) u
    have hcan' : canonical (which o) (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (retardedPhysicalIntegral (curriedPhase c.radialSection C) (if o=0 then W 0+W 1 else W 2)
          (endpointOutputMask f p output) (chartInputMask f p) β hs (z.1-c.maskRadius/2) u y) := by
      by_cases hzero : o=0 <;> simpa [which,hzero,W,Fs,selectedConicAmplitude] using hcan
    filter_upwards [hret,hcan'] with y hy hz
    exact hy.trans ((congrArg (WithLp.toLp 2) (htestEq o u y)).trans hz.symm)
  refine ⟨?_,?_,?_⟩
  · intro o
    calc
      ‖capped o‖ ≤ ‖Mo‖ * ‖(Op o).comp Mi‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (‖Op o‖ * 1) := mul_le_mul (norm_sourceCutMultiplier_le _ _ _)
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (norm_sourceCutMultiplier_le _ _ _) (norm_nonneg _)))
        (norm_nonneg _) zero_le_one
      _ = ‖Op o‖ := by ring
      _ ≤ base o := (hOp o).1
  · intro o u
    rw [hcanonical o]
    have hint := hcanonicalIntegral (which o) u
    have hint' : canonical (which o) u = elapsedGraphIntegral (3*c.maskRadius/4)
        (curriedPhase c.radialSection C) (if o=0 then W 0+W 1 else W 2)
        (endpointOutputMask f p output) (chartInputMask f p) β u := by
      by_cases hzero : o=0 <;> simpa [which,hzero,W,Fs,selectedConicAmplitude] using hint
    rw [hint',hβeq]
    unfold elapsedGraphIntegral
    simp_rw [hgraphEq]
  · intro o u
    rw [hcanonical o]
    have hadj := hcanonicalAdj (which o) u
    have hadj' : (canonical (which o)).adjoint u = ∫ t in Icc 0 (3*c.maskRadius/4),
        (elapsedGraph (curriedPhase c.radialSection C) (if o=0 then W 0+W 1 else W 2)
          (endpointOutputMask f p output) (chartInputMask f p) β t).adjoint u := by
      by_cases hzero : o=0 <;> simpa [which,hzero,W,Fs,selectedConicAmplitude] using hadj
    rw [hadj',hβeq]
    simp_rw [hgraphEq]

end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
