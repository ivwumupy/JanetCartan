module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutSource
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPrimaryInverseIndex
public import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometry
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalPhaseTemplate

/-!
# Actual native source and output phase for the uncut primary response

Consume the unchanged native Point44 → Source53/Observation39 producers.
The inverse/Fourier families retain the full original parameter windows; only
comparison with the actual physical atom is local on the prescribed θ-plateau.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 16000
open Set Metric Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalPrimary.OriginalUncutSource
open PhysicalInitialization PhysicalSeed

/-- Proof-only comparison neighborhood inside the plateau of the PRESCRIBED
parameter mask. All inverse and Fourier estimates stay on their original full
windows; this set only identifies their already θ-localized datum with the
actual physical atom near the original closed cell. -/
def parameterComparisonWindow {n : ℕ} (hn : 5 ≤ n) (a : OriginalPatchIndex hn)
    (cell : OriginalBoundary.centers hn a) : Set (Euclidean 3 × Euclidean (n-1)) :=
  interior {c | OriginalSourceProfiles.parameterCutoff hn a cell c = 1} ∩
    OriginalSourceMasks.parameterWindow hn a cell

/-- Every original closed parameter cell has an OPEN comparison neighborhood
where θ is identically one. The doubled window is not incorrectly declared a
θ-plateau (`app:ch_response:eq:response-full-map`). -/
theorem parameterComparisonWindow_spec {n : ℕ} (hn : 5 ≤ n) (a : OriginalPatchIndex hn)
    (cell : OriginalBoundary.centers hn a) :
    IsOpen (parameterComparisonWindow hn a cell) ∧
      parameterComparisonWindow hn a cell ⊆ OriginalSourceMasks.parameterWindow hn a cell ∧
      (∀ c ∈ parameterComparisonWindow hn a cell,
        OriginalSourceProfiles.parameterCutoff hn a cell c = 1) ∧
      closedBall (cell.1.1, (OriginalBoundary.T hn a).reference.spatialPatch cell.1.1)
        (OriginalBoundary.σcover hn a cell) ⊆ parameterComparisonWindow hn a cell := by
  have hV := OriginalSourceMasks.parameterWindow_spec hn a cell
  have hθ := OriginalSourceProfiles.parameterCutoff_spec hn a cell
  refine ⟨isOpen_interior.inter hV.1, inter_subset_right, ?_, ?_⟩
  · intro c hc
    exact interior_subset (s := {c | OriginalSourceProfiles.parameterCutoff hn a cell c = 1}) hc.1
  · intro c hc
    exact ⟨mem_interior_iff_mem_nhds.mpr (hθ.2.2.2 c hc), hV.2.2.2.2 hc⟩

open ActualCarriers.CurrentFullPhase ProtectedFlow ProjectedStressFrame
  LeadingWave.FullModulation ResponsePrimarySources

/-- The fixed phase collar and raw/extended-frame identity imply agreement
on the original protected source *including the cutoff shoulders*. This single
identity is restricted below; no per-output phase is reconstructed. -/
theorem phase_on_native_source_rectangle {n N : ℕ} (hn : 5 ≤ n) (a : OriginalPatchIndex hn)
    (F : Euclidean n → Euclidean N) (ext : BallExtension.Parameters (Euclidean n))
    (hcenter : ext.center = 0) (hradius : ext.radius = OriginalBoundary.b hn)
    (Q Qext : {q : Euclidean n → Fin n → MetricTensor n //
      ContDiffOn ℝ ∞ q (ball (0 : Euclidean n) (OriginalBoundary.R hn)) ∧
      cNorm (closedBall (0 : Euclidean n) (OriginalBoundary.T hn a).data.localReference.stateRadius)
        6 (q - fun _ ↦ cubeStress n) < (OriginalBoundary.T hn a).family.threshold})
    (hraw : Q.1 = projectedStress F) (hext : Qext.1 = extendedProjectedStress ext F)
    (χ : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → ℝ)
    (hχ : ∀ p ∈ OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a,
      χ =ᶠ[𝓝 p] fun _ ↦ 1)
    (φ : (Euclidean 3 × Euclidean (n-1)) → Euclidean n → ℝ)
    (he : φ = fun c x ↦ retainedPhaseExtension (OriginalBoundary.T hn a) Qext χ x c) :
    ∀ c ∈ OriginalProtected.Csrc hn a, EqOn (φ c)
      (fun x ↦ phase (OriginalBoundary.T hn a) Q x c.2) (OriginalProtected.Xsrc hn a) := by
  intro c hc x hx
  have hp := (OriginalProtected.source_domains hn a).2.2.2.1 (show
    (x,c) ∈ OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a from ⟨hx,hc⟩)
  have hplateau := OriginalUncutReconstruction.phase_cutoff_plateau_of_eventually_one χ hχ
    (show (x,c) ∈ OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a from ⟨hx,hc⟩)
  rw [he]
  apply (retainedPhaseExtension_physical_eventuallyEq (OriginalBoundary.T hn a) Qext hplateau).self_of_nhds.trans
  exact (original_native_extension_phase_eq hn a F ext hcenter hradius Q Qext hraw hext hp).symm

end JanetCartan.PhysicalPrimary.OriginalUncutSource

retain_source53_observation39_phase_frames
construct_original_physical_source_phase
restrict_original_physical_source_phase
