module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhaseProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedCurrent
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalWordGradientTemplate

/-!
# Exact original full-word physical and coordinate gradient ranges

The same original39 current, original positive physical cutoff phase and
unchanged whole word box satisfy the gradient inputs of the actual complete
residual/solver constructors. The gradient constants remain the original
Whole.wholeLo/wholeHi, before source scale and history; no reserve, sector,
new threshold, or analytic-success input is added.
Consumer: `MeasuredResidualAllCases` physical and coordinate gradient inputs
(`app:ch_response:eq:fixed-factor-transfer`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16000
@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalWordGradient
open PhysicalSeed PhysicalInitialization ActualCarriers FrozenMenu
open ActualCarriers.CurrentFullPhase CompatibleResponse HamiltonPhase
open LeadingWave.FullModulation ProtectedFlow ProjectedStressFrame
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.FiniteMasks.ActualFamily

/-- The literal original positive physical phase, with its prescribed cutoff
and admitted frame; this definition makes no selection
(`app:ch_response:eq:fixed-factor-transfer`). -/
def original_physical_phase {d : ℕ} (hn : 5 ≤ d+1) (a : OriginalPatchIndex hn)
    (χ : Euclidean (d+1) × (Euclidean 3 × Euclidean d) → ℝ)
    (Q : {Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1) //
      ContDiffOn ℝ ∞ Q (ball 0 (OriginalBoundary.R hn)) ∧
      cNorm (closedBall (0 : Euclidean (d+1))
        (OriginalBoundary.T hn a).data.localReference.stateRadius) 6
        (Q-fun _ ↦ cubeStress (d+1)) < (OriginalBoundary.T hn a).family.threshold}) :
    Euclidean (d+1) × (Euclidean 3 × Euclidean d) → ℝ :=
  fun q ↦ χ q * phase (OriginalBoundary.T hn a) Q q.1 q.2.2

/-- The same original whole-source cutoff germ gives the actual full-phase
physical germ before any reserve or history-profile threshold is needed
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem original_physical_phase_germ {d : ℕ} (hn : 5 ≤ d+1) (a : OriginalPatchIndex hn)
    (χ : Euclidean (d+1) × (Euclidean 3 × Euclidean d) → ℝ) (Q : _)
    (hχ : ∀ q : Euclidean (d+1) × (Euclidean 3 × Euclidean d),
      q ∈ OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a → χ =ᶠ[𝓝 q] fun _ ↦ 1) :
    ∀ q : Euclidean (d+1) × (Euclidean 3 × Euclidean d),
      q ∈ OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a →
      original_physical_phase hn a χ Q =ᶠ[𝓝 q]
        fun p ↦ phase (OriginalBoundary.T hn a) Q p.1 p.2.2 := by
  intro q hq
  filter_upwards [hχ q hq] with p hp
  change χ p * phase (OriginalBoundary.T hn a) Q p.1 p.2.2 = _
  rw [hp,one_mul]

private theorem physicalCoordinates_primary_symm {d : ℕ} (i : Fin (d+1)) (y : Euclidean (d+1)) :
    (primaryCoordinateChange i).symm y = physicalCoordinates i y := rfl

private theorem physicalCoordinates_zero {d : ℕ} (y : Euclidean (d+1)) :
    physicalCoordinates (0 : Fin (d+1)) y = y :=
  (RegularSector.Characteristic.coordinateSplit 0).symm_apply_apply y

/-- Restrict the existing whole-source germ and gradient band to the unchanged
physical/coordinate word boxes. This chooses no phase, margin or constants
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem full_word_gradient_ranges_of_germ {d : ℕ} (hn : 5 ≤ d+1) (a : OriginalPatchIndex hn)
    (r : ℝ) (Q : _) (lo hi : ℝ)
    (φ : Euclidean (d+1) × (Euclidean 3 × Euclidean d) → ℝ)
    (hsubset : closedBall (0 : Euclidean (d+1)) r ×ˢ closure (OriginalRegular.wholeWindow hn a) ⊆
      OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a)
    (hgerm : ∀ q : Euclidean (d+1) × (Euclidean 3 × Euclidean d),
      q ∈ OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a →
      φ =ᶠ[𝓝 q] fun p ↦ phase (OriginalBoundary.T hn a) Q p.1 p.2.2)
    (hband : ∀ index : Fin (d+1), ∀ y : Euclidean (d+1),
      (primaryCoordinateChange index).symm y ∈ OriginalProtected.Xsrc hn a →
      ∀ b : Euclidean 3 × Euclidean d, b ∈ OriginalProtected.Csrc hn a →
      lo ≤ ‖fderiv ℝ (fun z ↦ (OriginalBoundary.T hn a).fullSourcePhaseInCoordinates index Q z b) y‖ ∧
      ‖fderiv ℝ (fun z ↦ (OriginalBoundary.T hn a).fullSourcePhaseInCoordinates index Q z b) y‖ ≤ hi) :
    (∀ b ∈ OriginalRegular.wholeWindow hn a, ∀ y ∈ ball (0 : Euclidean (d+1)) r,
      lo ≤ ‖fderiv ℝ (fun z ↦ φ (z,b)) y‖ ∧ ‖fderiv ℝ (fun z ↦ φ (z,b)) y‖ ≤ hi) ∧
    ∀ index : Fin (d+1), ∀ b ∈ OriginalRegular.wholeWindow hn a,
      ∀ y ∈ ball ((physicalCoordinates index).symm (0 : Euclidean (d+1))) r,
      lo ≤ ‖fderiv ℝ (fun z ↦ φ (physicalCoordinates index z,b)) y‖ ∧
      ‖fderiv ℝ (fun z ↦ φ (physicalCoordinates index z,b)) y‖ ≤ hi := by
  have hc (index : Fin (d+1)) (b : Euclidean 3 × Euclidean d)
      (hb : b ∈ OriginalRegular.wholeWindow hn a) (y : Euclidean (d+1))
      (hy : y ∈ ball ((physicalCoordinates index).symm (0 : Euclidean (d+1))) r) :
      lo ≤ ‖fderiv ℝ (fun z ↦ φ (physicalCoordinates index z,b)) y‖ ∧
      ‖fderiv ℝ (fun z ↦ φ (physicalCoordinates index z,b)) y‖ ≤ hi := by
    have hyphys : physicalCoordinates index y ∈ ball (0 : Euclidean (d+1)) r := by
      simpa only [map_zero,mem_ball_zero_iff,norm_physicalCoordinates] using hy
    have hpoint : (physicalCoordinates index y,b) ∈
        OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a :=
      hsubset ⟨ball_subset_closedBall hyphys,subset_closure hb⟩
    have hg := (hgerm (physicalCoordinates index y,b) hpoint).comp_tendsto
      (((physicalCoordinates index).continuous.prodMk continuous_const).tendsto y)
    have he : (fun z ↦ φ (physicalCoordinates index z,b)) =ᶠ[𝓝 y]
        (fun z ↦ (OriginalBoundary.T hn a).fullSourcePhaseInCoordinates index Q z b) := by
      simpa only [Function.comp_def,PatchQuantitativeFamily.fullSourcePhaseInCoordinates,
        physicalCoordinates_primary_symm] using hg
    rw [he.fderiv_eq]
    exact hband index y (by simpa only [physicalCoordinates_primary_symm] using hpoint.1) b hpoint.2
  refine ⟨?_,hc⟩
  intro b hb y hy
  simpa only [physicalCoordinates_zero] using
    hc 0 b hb y (by simpa only [map_zero] using hy)

apply_original_whole_word_gradient_ranges

end JanetCartan.PhysicalPrimary.OriginalWordGradient
