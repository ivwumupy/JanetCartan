module
public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.FullPhaseCompact

/-!
# Frozen angular protection for independent covector shifts

The literal frozen Hamilton momentum is continuous on its original target.
Compactness of the original carrier graph gives one quantitative radius for
independent covector shifts, before any current frame or finite history.
This supplies the fixed geometric input of the full-source localization lemma
when the original parameter compact lies in that same radius.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.InitialSourceLocalization
open ActualCarriers CurrentFullPhase FrozenMenu HamiltonPhase ProtectedFlow
open ArbitraryAccuracy.ProtectedMasks ActualCarriers.FrozenPhaseReference

/-- A fixed angular margin on the literal frozen carrier graph gives one
positive radius for independent full-covector shifts. This produces the
frozen full-phase angular input for
`exists_retained_admittedSource_firstMask_rapidDecayAt`
(`app:ch_seed:prop:seed-actual-menu`, `app:ch_regular:eq:source-tail`). -/
theorem exists_frozen_fullPhase_angular_shift_radius
    {d : ℕ} {P : Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {S : Set (Euclidean (d+1))} (hS : IsCompact S)
    (hSball : S ⊆ ball (0 : Euclidean (d+1)) T.physicalRadius)
    {Ω : Set (Euclidean (d+1))}
    (hangular : ∀ z ∈ parameterCube P.radius,
      normalizedCovector (P.toFun z) ∈ interior Ω) :
    ∃ ε > (0 : ℝ), ∀ x ∈ S, ∀ z ∈ parameterCube P.radius,
      ∀ v : Euclidean (d+1-1), ‖v‖ ≤ ε →
        (x,(0,T.reference.spatialPatch z + v)) ∈ T.reference.chart.target ∧
        normalizedCovector
          (T.reference.chart.chartMomentum (x,(0,T.reference.spatialPatch z + v))) ∈
          interior Ω := by
  let F : Euclidean (d+1) × Euclidean 3 →
      Euclidean (d+1) × (ℝ × Euclidean (d+1-1)) := fun w ↦ (w.1,(0,T.reference.spatialPatch w.2))
  let K := F '' (S ×ˢ parameterCube P.radius)
  have hsp : ContinuousOn T.reference.spatialPatch (parameterCube P.radius) :=
    (T.reference.spatialPatch_smooth hP).continuousOn.mono
      (parameterCube_subset_doubledInterior hP.1)
  have hF : ContinuousOn F (S ×ˢ parameterCube P.radius) :=
    continuousOn_fst.prodMk (continuousOn_const.prodMk (hsp.comp continuousOn_snd
      (fun _ hw ↦ hw.2)))
  have hK : IsCompact K := (hS.prod (isCompact_parameterCube _)).image_of_continuousOn hF
  let O := (fun ξ : Euclidean (d+1) ↦ ((0 : Euclidean (d+1)),ξ)) ⁻¹'
    physicalProtectedRegion Ω
  have hO : IsOpen O := (isOpen_physicalProtectedRegion Ω).preimage
    (continuous_const.prodMk continuous_id)
  let V := T.reference.chart.target ∩ T.reference.chart.chartMomentum ⁻¹' O
  have hV : IsOpen V := (T.reference.chart.contDiffOn_chartMomentum
    T.reference.momentum_smooth T.reference.coordinates_smooth).continuousOn.isOpen_inter_preimage
      T.reference.chart.isOpen_target hO
  have hKV : K ⊆ V := by
    rintro _ ⟨⟨x,z⟩,⟨hx,hz⟩,rfl⟩
    have ht := T.reference.target_contains x (hSball hx) z
      (parameterCube_subset_doubledInterior hP.1 hz)
    have he : T.reference.chart.chartMomentum (F (x,z)) = P.toFun z :=
      (chartMomentum_eq_of_phase_linear T.reference.chart T.reference.covector
        T.reference.phase_linear ht).trans
        (T.reference.patch_covector z (parameterCube_subset_doubledInterior hP.1 hz))
    refine ⟨ht,?_⟩
    have ha := T.reference.chart.source_admissible _
      (T.reference.chart.maps_to_source _ ht)
    have hne := (mem_frozenSymbol_domain _).mp (T.reference.flow.state_mem _ ha.1 _ ha.2)
    change _ ≠ 0 ∧ normalizedCovector _ ∈ interior Ω
    refine ⟨hne,?_⟩
    rw [he]
    exact hangular z hz
  obtain ⟨ε,hε,hbuffer⟩ := hK.exists_cthickening_subset_open hV hKV
  refine ⟨ε,hε,?_⟩
  intro x hx z hz v hv
  have hd : dist (x,(0,T.reference.spatialPatch z + v)) (F (x,z)) ≤ ε := by
    dsimp only [F]
    rw [Prod.dist_eq,Prod.dist_eq,dist_self,dist_self]
    simpa only [dist_eq_norm,add_sub_cancel_left,max_eq_right (norm_nonneg v)] using hv
  have hmem := hbuffer (mem_cthickening_of_dist_le _ _ _ K ⟨(x,z),⟨hx,hz⟩,rfl⟩ hd)
  exact ⟨hmem.1,hmem.2.2⟩

/-- Independent covectors in the constructed fixed shift radius have one
symmetric source compact for every admitted current phase. Both the original
phase domain and the frozen angular hypothesis are proved for this compact;
the initializer retains the original parameter set inside the returned radius
(`app:ch_seed:prop:seed-actual-menu`, `app:ch_regular:eq:source-tail`). -/
theorem exists_retained_fullPhase_source_compact_for_covector_shifts
    {d : ℕ} {P : Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {S : Set (Euclidean (d+1))} (hS : IsCompact S)
    (hSball : S ⊆ ball (0 : Euclidean (d+1)) T.physicalRadius)
    {Ω : Set (Euclidean (d+1))} (hΩsym : ∀ ξ ∈ Ω, -ξ ∈ Ω)
    (hangular : ∀ z ∈ parameterCube P.radius,
      normalizedCovector (P.toFun z) ∈ interior Ω) :
    ∃ ε > (0 : ℝ),
    ∀ Cpar : Set (Euclidean 3 × Euclidean (d+1-1)), IsCompact Cpar →
      (∀ c ∈ Cpar, c.1 ∈ parameterCube P.radius ∧
        ‖c.2 - T.reference.spatialPatch c.1‖ ≤ ε) →
      S ×ˢ Cpar ⊆ LeadingWave.FullModulation.domain T ∧
      (∀ w ∈ S ×ˢ Cpar,
        normalizedCovector (T.reference.chart.chartMomentum (w.1,(0,w.2.2))) ∈ interior Ω) ∧
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
    ∃ Ksource : Set (Euclidean (d+1)), IsCompact Ksource ∧
      (∀ ξ ∈ Ksource, -ξ ∈ Ksource) ∧
      (∀ ξ ∈ Ksource, ξ ≠ 0 ∧ normalizedCovector ξ ∈ Ω) ∧
      ∀ Q, cNorm (closedBall (0 : Euclidean (d+1)) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d+1)) < δ →
      ∀ x ∈ S, ∀ c ∈ Cpar,
        (x, gradient (fun y ↦ LeadingWave.FullModulation.phase T Q y c.2) x) ∈
          S ×ˢ Ksource := by
  obtain ⟨ε,hε,hshift⟩ := exists_frozen_fullPhase_angular_shift_radius T hP hS hSball hangular
  refine ⟨ε,hε,?_⟩
  intro Cpar hCpar hpar
  have hgeometry (w) (hw : w ∈ S ×ˢ Cpar) :
      (w.1,(0,w.2.2)) ∈ T.reference.chart.target ∧
        normalizedCovector (T.reference.chart.chartMomentum (w.1,(0,w.2.2))) ∈ interior Ω := by
    simpa only [add_sub_cancel] using hshift w.1 hw.1 w.2.1 (hpar w.2 hw.2).1
      (w.2.2 - T.reference.spatialPatch w.2.1) (hpar w.2 hw.2).2
  have hsource : S ×ˢ Cpar ⊆ LeadingWave.FullModulation.domain T := by
    intro w hw
    exact (LeadingWave.FullModulation.inclusion_mem_ball T).mp (hgeometry w hw).1
  have hfrozen := fun w hw ↦ (hgeometry w hw).2
  exact ⟨hsource,hfrozen,
    exists_retained_fullPhase_source_frequency_compact T hS hCpar hsource hΩsym hfrozen⟩

end JanetCartan.InitialSourceLocalization
