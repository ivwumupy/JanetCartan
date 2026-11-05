module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.PhaseBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly.Buffers

@[expose] public noncomputable section
open Set Metric
namespace JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu LeadingWave.FullModulation

/-- The original doubled source cell supplies the selector's compact spatial
and full-covector parameter domains. The covector bound is the literal output
of `CorrectedAtoms.exists_common_initialized_history_primary_correction_with_source_geometry`;
no carrier restriction or independently chosen cell enters. Consumer:
`exists_pre_reference_terminal_history_characteristic_source_envelopes`
(`new:sec:order-of-choices`, `app:ch_response:eq:direct-envelope-profile`). -/
theorem original_cell_compact_source_domain
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) (z₀ : Euclidean 3)
    {σ RQ : ℝ} (hσ : 0 < σ) (hRQ : RQ < T.family.radius)
    (hcellCovector : ∀ w ∈ closedBall
      ((0 : Euclidean n), (z₀,T.reference.spatialPatch z₀)) (2*σ),
      w.2.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T)
        (min T.family.radius (3*T.family.sourceRadius))) :
    IsCompact (closedBall (0 : Euclidean n) RQ) ∧
    IsCompact (closedBall (z₀,T.reference.spatialPatch z₀) (2*σ)) ∧
    (∀ c ∈ closedBall (z₀,T.reference.spatialPatch z₀) (2*σ),
      c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius) ∧
    closedBall (0 : Euclidean n) RQ ×ˢ
      closedBall (z₀,T.reference.spatialPatch z₀) (2*σ) ⊆ domain T := by
  have hcov (c) (hc : c ∈ closedBall (z₀,T.reference.spatialPatch z₀) (2*σ)) :
      c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius := by
    apply ball_subset_ball (min_le_left ..)
    apply hcellCovector (0,c)
    rw [← closedBall_prod_same]
    exact ⟨mem_closedBall_self (by positivity),hc⟩
  refine ⟨isCompact_closedBall _ _,isCompact_closedBall _ _,hcov,?_⟩
  intro w hw
  change (w.1,w.2.2) ∈ phaseDomain T
  rw [phaseDomain,← ball_prod_same]
  exact ⟨closedBall_subset_ball hRQ hw.1,hcov w.2 hw.2⟩

/-- Choose one spatial selector radius for the original finite collection of
full-source cells. Every doubled parameter cell is unchanged, and all compact
domains lie in the same original full-phase domains. Consumer:
`exists_pre_reference_terminal_history_characteristic_source_envelopes`
(`new:sec:order-of-choices`, `app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_original_cells_common_source_domain
    {n : ℕ} {ι : Type*} [Finite ι] {U : Set (Euclidean n)} {hU : IsOpen U}
    (P : ι → Patch n) (T : ∀ i, PatchQuantitativeFamily (P i) U hU)
    (z : ι → Euclidean 3) (σ : ι → ℝ) (hσ : ∀ i, 0 < σ i)
    (hcellCovector : ∀ i, ∀ w ∈ closedBall
      ((0 : Euclidean n), (z i,(T i).reference.spatialPatch (z i))) (2*σ i),
      w.2.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter (T i))
        (min (T i).family.radius (3*(T i).family.sourceRadius)))
    {R : ℝ} (hR : 0 < R) :
    ∃ RQ > (0 : ℝ), RQ < R ∧
      closedBall (0 : Euclidean n) RQ ⊆ ball 0 R ∧
      IsCompact (closedBall (0 : Euclidean n) RQ) ∧
      ∀ i, RQ < (T i).family.radius ∧
        closedBall (0 : Euclidean n) RQ ⊆ ball 0 (T i).physicalRadius ∧
        IsCompact (closedBall (z i,(T i).reference.spatialPatch (z i)) (2*σ i)) ∧
        (∀ c ∈ closedBall (z i,(T i).reference.spatialPatch (z i)) (2*σ i),
          c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter (T i)) (T i).family.radius) ∧
        closedBall (0 : Euclidean n) RQ ×ˢ
          closedBall (z i,(T i).reference.spatialPatch (z i)) (2*σ i) ⊆ domain (T i) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨r,δ,K,hr,_,_,_,hcommon⟩ := exists_common_phase_buffers
    (fun i ↦ min (T i).family.radius (T i).physicalRadius)
    (fun _ : ι ↦ (1 : ℝ)) (fun _ : ι ↦ (1 : ℝ))
    (fun i ↦ lt_min (T i).family.radius_pos (T i).physicalRadius_pos) (fun _ ↦ by norm_num)
  let RQ := min r (R/2)
  have hRQ : 0 < RQ := lt_min hr (half_pos hR)
  have hRQR : RQ < R := (min_le_right r (R/2)).trans_lt (half_lt_self hR)
  refine ⟨RQ,hRQ,hRQR,closedBall_subset_ball hRQR,isCompact_closedBall _ _,?_⟩
  intro i
  have hrmin : r < min (T i).family.radius (T i).physicalRadius := by
    linarith only [(hcommon i).1,hr]
  have hRQphase : RQ < (T i).family.radius :=
    (min_le_left r (R/2)).trans_lt (hrmin.trans_le (min_le_left ..))
  have hRQphysical : RQ < (T i).physicalRadius :=
    (min_le_left r (R/2)).trans_lt (hrmin.trans_le (min_le_right ..))
  have hd := original_cell_compact_source_domain (T i) (z i) (hσ i) hRQphase (hcellCovector i)
  exact ⟨hRQphase,closedBall_subset_ball hRQphysical,hd.2.1,hd.2.2⟩


end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
