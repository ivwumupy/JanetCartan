module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedGeometry
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedWholeTemplate

/-! The original common physical phase is identically one on the ENTIRE
retarded physical box times the closure of the original whole measurement
window. This is additional to the already proved active-incidence germ; no
whole window is replaced by an active set. Consumer: the native application of
`exists_physical_history_measured_residual_hstep` and the final solver step
(`app:ch_response:eq:response-whole-source-partition`). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16000
open Set Metric Filter
open scoped Topology
namespace JanetCartan.PhysicalPrimary.OriginalRetardedWhole
open PhysicalInitialization

/-- Pull back only the original physical cutoff germ. The full label and
independent covector are left unchanged, as is the entire physical box. -/
theorem whole_germ_pullback {d : ℕ} (i : Fin (d+1))
    {X Y : Set (Euclidean (d+1))} {V : Set (Euclidean 3 × Euclidean d)}
    {χ : Euclidean (d+1) × (Euclidean 3 × Euclidean d) → ℝ}
    (hY : MapsTo (CompatibleResponse.primaryCoordinateChange i).symm Y X)
    (hχ : ∀ q ∈ X ×ˢ closure V, χ =ᶠ[𝓝 q] fun _ ↦ 1) :
    ∀ q ∈ Y ×ˢ closure V,
      χ ∘ OriginalRegular.sectorToPhysical i =ᶠ[𝓝 q] fun _ ↦ 1 := by
  intro q hq
  have hp : OriginalRegular.sectorToPhysical i q ∈ X ×ˢ closure V := ⟨hY hq.1,hq.2⟩
  exact (hχ _ hp).comp_tendsto
    (OriginalRegular.sectorToPhysical_smooth i).continuous.continuousAt.tendsto

/-- The closure of the original whole window, not just the source support or
an active sector, has the original full-phase covector admission. -/
theorem whole_window_covectors {d : ℕ} (hn : 5 ≤ d+1) (a : OriginalPatchIndex hn) :
    ∀ c ∈ closure (OriginalRegular.wholeWindow hn a),
      c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter (PhysicalSeed.OriginalBoundary.T hn a))
        (PhysicalSeed.OriginalBoundary.T hn a).family.radius :=
  fun c hc ↦ (OriginalProtected.source_domains hn a).2.2.1 c
    ((OriginalRegular.wholeWindow_spec hn a).2.2.1 hc)

retain_original_whole_box_phase_germ

end JanetCartan.PhysicalPrimary.OriginalRetardedWhole
