module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RawCappedInitialization.CorrectedSelection
public meta import JanetCartan.Iteration.PhysicalSeed.AngularTemplates

/-!
# Both original spatial and angular caps in the same incidence selection

The original `aExtra` caps both detector widths before the one finite choice.
This is the actual missing geometric input to
`PhysicalSampling.exists_original_scalar_sampling_bounds`, for
`app:ch_waves:eq:sampling-operator-bounds`. No selected radius is shrunk.
-/

set_option warningAsError true
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalSeed.AngularSelection
open ContinuumRow ContinuumRow.NormalizedSelection
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormal ContinuumNormal.RetainedFrozen ContinuumNormal.FrozenModel
open ContinuumNormalReduction TransportSymbol FullPhaseCharts ActualPhase ActualComparison
open CarrierVariation.FamilyInputs PositiveReference ProjectedStressFrame
open NullTransport ActualFlow FlowAmplitude CarrierSobolev
open ContinuumAdjoint ContinuumAdjoint.Canonical ContinuumAdjoint.DensityMultiplier
open ContinuumAdjoint.Canonical.NormalInputs ContinuumAdjoint.Canonical.PhaseExtension CommonMeasurement

declare_angular_retained exists_corrected_row_with_angular_cap
  from JanetCartan.ContinuumRow.NormalizedSelection.exists_finite_incidence_row_with_corrected_rawAdjoints
  before b retaining
    (∀ i, angularWidth (ηb i) (r' i) ≤ (aExtra i.1.1 i.2 (cell i.1.1 i.2)).1) := by
  classical
  have hpatch (b) (l) (j) : Ω b l j ⊆
      ball (0 : Euclidean n) (T b l).physicalRadius ×ˢ parameterCube (2 * (D.patches b l).radius) := by
    intro p hp
    exact ⟨(hpatchStrong b l j hp).1.2,
      fun k ↦ ((hpatchStrong b l j hp).2 k).le.trans (by
        have := (hD.2.2.2.2.1 b l).1.1
        linarith)⟩
  have hk (p : IncidenceCenter D) : p.1.2 ≠ 0 := by
    intro hzero
    have hs := p.2.1
    simp [hzero] at hs
  have hz (p : IncidenceCenter D) (l : Fin (D.patchCount p.1.1)) :=
    ((hD.2.2.2.2.1 p.1.1 l).2.2.1 p.1.2 p.2.2).1
  have hinc (p : IncidenceCenter D) (l : Fin (D.patchCount p.1.1)) :=
    ((hD.2.2.2.2.1 p.1.1 l).2.2.1 p.1.2 p.2.2).2.2.2
  have hd (p : IncidenceCenter D) (l : Fin (D.patchCount p.1.1)) :
      fderiv ℝ (fun w ↦ incidence p.1.2 ((D.patches p.1.1 l).toFun w))
        (D.roots p.1.1 l p.1.2) (EuclideanSpace.single 0 1) ≠ 0 :=
    abs_pos.mp (hD.1.trans_le ((hD.2.2.2.2.1 p.1.1 l).2.2.2 p.1.2 p.2.2 _
      (fun k ↦ (hz p l k).le)))
  let AdmissibleCell := fun (p : IncidenceCenter D) (l : Fin (D.patchCount p.1.1)) ↦
    {j : I p.1.1 l // (D.roots p.1.1 l p.1.2 0,
      spectatorCenter (D.roots p.1.1 l p.1.2)) ∈ V p.1.1 l j}
  choose aCap bCap haCap hbCap _haCap χcorrected σlocal hσlocal _hσone hsub using
    fun (p : IncidenceCenter D) (l : Fin (D.patchCount p.1.1)) (j : AdmissibleCell p l) ↦
      ContinuumInverse.exists_corrected_seed_rawAdjoint_for_submasks H
        (hD.2.2.2.2.1 p.1.1 l).1 (T p.1.1 l) hUH hbounded
        (hΩ p.1.1 l j.1) (hKΩ p.1.1 l j.1) (hpatchStrong p.1.1 l j.1)
        (hM p.1.1 l j.1) (hτeq p.1.1 l j.1) (hΩscale p.1.1 l j.1)
        (hRc p.1.1 l j.1) (hτ p.1.1 l j.1) (hτR p.1.1 l j.1)
        (hbuffer p.1.1 l j.1) (hphysical p.1.1 l) (c₀ p.1.1 l j.1)
        (htrans p.1.1 l j.1) (hR p.1.1 l j.1) (hRphysical p.1.1 l j.1)
        (hRU p.1.1 l j.1) (hV p.1.1 l j.1) (hVP p.1.1 l j.1)
        (hflow p.1.1 l j.1) (hL p.1.1 l j.1) (hMforward p.1.1 l j.1)
        (hforward p.1.1 l j.1) (hRtime p.1.1 l j.1) (hlabel p.1.1 l j.1)
        (hz p l) j.2 (hk p) (hinc p l) (hd p l) hcap
  let spatialCap := fun (p : IncidenceCenter D) (l : Fin (D.patchCount p.1.1)) (j : I p.1.1 l) ↦
    if hj : (D.roots p.1.1 l p.1.2 0, spectatorCenter (D.roots p.1.1 l p.1.2)) ∈ V p.1.1 l j
      then min (aCap p l ⟨j, hj⟩) (aExtra p l j).1 else (aExtra p l j).1
  let angularCap := fun (p : IncidenceCenter D) (l : Fin (D.patchCount p.1.1)) (j : I p.1.1 l) ↦
    if hj : (D.roots p.1.1 l p.1.2 0, spectatorCenter (D.roots p.1.1 l p.1.2)) ∈ V p.1.1 l j
      then min (bCap p l ⟨j, hj⟩) (aExtra p l j).1 else (aExtra p l j).1
  have hspatialCap (p) (l) (j) : 0 < spatialCap p l j := by
    dsimp only [spatialCap]
    split_ifs with hj
    · exact lt_min (haCap p l ⟨j, hj⟩) (aExtra p l j).2
    · exact (aExtra p l j).2
  have hangularCap (p) (l) (j) : 0 < angularCap p l j := by
    dsimp only [angularCap]
    split_ifs with hj
    · exact lt_min (hbCap p l ⟨j, hj⟩) (aExtra p l j).2
    · exact (aExtra p l j).2
  obtain ⟨cell, hcell, centers, εcover, hεcover, hcover', hdomain, hgram,
    t, r, a, r', a', ht, hr, ha, hr', ha', hcell', hηb, htnorm, hdir, hcaps,
    hboxes, hmask, b, hb, hbcell, hbH, hbhalf, hba, hsampling,
    δ, hδ, hgeometry, hrawUncorrected⟩ :=
    exists_finite_incidence_geometry_rawAdjoints_and_sampling_with_prescribed_caps hD H hUH hbounded
      T I Ω hΩ zCell ρc Rc M τlead row col hKΩ hpatch hRc hτ hτR hbuffer hphysical c₀ htrans
      R V hR hRphysical hRU hV hVP hflow hcover spatialCap angularCap hspatialCap hangularCap hcap
  let ι := (j : centers) × Fin (D.patchCount j.1.1.1)
  let selected := fun i : ι ↦ (⟨cell i.1.1 i.2, (hcell i.1.1 i.2).2⟩ : AdmissibleCell i.1.1 i.2)
  have hsourceCap (i : ι) : a' i ≤ min (aCap i.1.1 i.2 (selected i))
      (aExtra i.1.1 i.2 (cell i.1.1 i.2)).1 := by
    simpa only [spatialCap, dite_eq_left (hcell i.1.1 i.2).2, selected] using (hcaps i).1
  have hExtraCap (i : ι) : a' i ≤ (aExtra i.1.1 i.2 (cell i.1.1 i.2)).1 :=
    (hsourceCap i).trans (min_le_right _ _)
  have hangularSourceCap (i : ι) : angularWidth
      ((T i.1.1.1.1 i.2).data.adapted.embedding.toContinuousLinearMap.adjoint
        (t i • i.1.1.1.2)) (r' i) ≤ min (bCap i.1.1 i.2 (selected i))
          (aExtra i.1.1 i.2 (cell i.1.1 i.2)).1 := by
    simpa only [angularCap, dite_eq_left (hcell i.1.1 i.2).2, selected] using (hcaps i).2
  have hAngularExtraCap (i : ι) := (hangularSourceCap i).trans (min_le_right _ _)
  obtain ⟨sCorrected, hsCorrected, hsle⟩ :=
    (finite_range (fun i : ι ↦ σlocal i.1.1 i.2 (selected i))).isCompact.exists_forall_le'
      continuousOn_id (by rintro d ⟨i, rfl⟩; exact hσlocal i.1.1 i.2 (selected i))
  refine ⟨cell, hcell, centers, εcover, hεcover, hcover', hdomain, hgram,
    t, r, a, r', a', ht, hr, ha, hr', ha', hcell', hηb, htnorm, hdir, hExtraCap,
    hboxes, hmask, hAngularExtraCap, b, hb, hbcell, hbH, hbhalf, hba, hsampling,
    δ, hδ, hgeometry, hrawUncorrected,
    min sCorrected 1, lt_min hsCorrected zero_lt_one, min_le_right _ _, ?_⟩
  intro i
  have hasub : a' i ≤ aCap i.1.1 i.2 (selected i) :=
    (hsourceCap i).trans (min_le_left _ _)
  have hbsub := (hangularSourceCap i).trans (min_le_left _ _)
  obtain ⟨hcellCorrected, hchart, Craw, Lraw, hCraw, hLraw, hraw⟩ :=
    hsub i.1.1 i.2 (selected i) (a' i) _ (ha' i)
      (angularWidth_spec (hηb i) (hr' i)).1 hasub hbsub
  refine ⟨χcorrected i.1.1 i.2 (selected i), hchart, Craw, Lraw, hCraw, hLraw, ?_⟩
  intro σ hσ v hv hinterval hlow
  have hηdir : NormedSpace.normalize
      ((T i.1.1.1.1 i.2).data.adapted.embedding.toContinuousLinearMap.adjoint
        (t i • i.1.1.1.2)) = NormedSpace.normalize
      ((T i.1.1.1.1 i.2).data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.1.2) := by
    rw [map_smul]
    exact NormedSpace.normalize_smul_of_pos (ht i) _
  simpa only [hηdir] using hraw σ
    ⟨hσ.1, (hσ.2.trans (min_le_left _ _)).trans (hsle _ ⟨i, rfl⟩)⟩ v hv hinterval hlow

end JanetCartan.PhysicalSeed.AngularSelection
