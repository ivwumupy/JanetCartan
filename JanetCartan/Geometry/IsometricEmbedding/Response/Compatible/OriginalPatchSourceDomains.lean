module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.OriginalSourceDomains

/-!
# Compact source domains for the original patch indexing

The original initializer retains finitely many doubled full-covector cells
inside each primary patch. Apply the common source-domain constructor to those
literal cells, then take their finite union in each original patch. This gives
the source domains required by the envelope selector without replacing the
patch family or any of its cells.
-/

@[expose] public noncomputable section
open Set Metric
namespace JanetCartan.CompatibleResponse
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu LeadingWave.FullModulation
open ResponseTransfer.RetainedCharacteristicEnvelopes

/-- The original doubled source cells give compact domains on the initializer's
original patch index. Their union retains every independent full covector and
uses one spatial radius before reference dilation and histories. Consumer:
`exists_common_initialized_envelope_normalized_inverse`
(`new:sec:order-of-choices`, `app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_original_patch_source_domains
    {n : ℕ} (D : CoverData n) {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    (centers : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      Finset (parameterCube (D.patches i.1 i.2).radius))
    (σ : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) → centers i → ℝ)
    (hσ : ∀ i j, 0 < σ i j)
    (hcellCovector : ∀ i j, ∀ w ∈ closedBall
      ((0 : Euclidean n), (j.1.1,(T i).reference.spatialPatch j.1.1)) (2*σ i j),
      w.2.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter (T i))
        (min (T i).family.radius (3*(T i).family.sourceRadius)))
    {R : ℝ} (hR : 0 < R) :
    let Csrc := fun i ↦ ⋃ j : centers i,
      closedBall (j.1.1,(T i).reference.spatialPatch j.1.1) (2*σ i j)
    ∃ RQ > (0 : ℝ), RQ < R ∧
      closedBall (0 : Euclidean n) RQ ⊆ ball 0 R ∧
      IsCompact (closedBall (0 : Euclidean n) RQ) ∧
      ∀ i, IsCompact (Csrc i) ∧
        (∀ c ∈ Csrc i,
          c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter (T i)) (T i).family.radius) ∧
        closedBall (0 : Euclidean n) RQ ×ˢ Csrc i ⊆ domain (T i) ∧
        closedBall (0 : Euclidean n) RQ ⊆ ball 0 (T i).physicalRadius := by
  classical
  intro Csrc
  let Cell := (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) × centers i
  obtain ⟨rphysical,hrphysical,hsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : (j : Fin D.chartCount) × Fin (D.patchCount j) ↦ (0 : ℝ))
    (y := fun i ↦ (T i).physicalRadius) (fun i ↦ (T i).physicalRadius_pos)
  obtain ⟨RQ,hRQ,hRQR,_,hcompact,hcell⟩ := exists_original_cells_common_source_domain
    (fun p : Cell ↦ D.patches p.1.1 p.1.2) (fun p ↦ T p.1)
    (fun p ↦ p.2.1.1) (fun p ↦ σ p.1 p.2)
    (fun p ↦ hσ p.1 p.2) (fun p ↦ hcellCovector p.1 p.2) (lt_min hR hrphysical)
  have hRQR' : RQ < R := hRQR.trans_le (min_le_left ..)
  refine ⟨RQ,hRQ,hRQR',closedBall_subset_ball hRQR',hcompact,?_⟩
  intro i
  refine ⟨isCompact_iUnion (fun j ↦ (hcell ⟨i,j⟩).2.2.1),?_,?_,?_⟩
  · intro c hc
    obtain ⟨j,hj⟩ := mem_iUnion.mp hc
    exact (hcell ⟨i,j⟩).2.2.2.1 c hj
  · intro w hw
    obtain ⟨j,hj⟩ := mem_iUnion.mp hw.2
    exact (hcell ⟨i,j⟩).2.2.2.2 ⟨hw.1,hj⟩
  · apply closedBall_subset_ball
    exact (hRQR.trans_le (min_le_right ..)).trans (by simpa using hsmall i)

end JanetCartan.CompatibleResponse
