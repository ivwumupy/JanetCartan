module

public import JanetCartan.Iteration.PhysicalSeed.SelectedBoundary

/-!
# Actual original roots in the fixed leading and comparison windows

The original carrier-label membership places the literal incident root in the
SAME static leading cell. These windows were chosen before every immersion and
scalar budget; they are not the later `CurrentLeading.c` lower gap. The actual
21-argument specialization uses `SelectedBoundary.fact1`, without selecting a
new parent, radius, reference, scalar, or leading flow.

Consumers: the ONE shared pre-source working ball of `PhysicalSampling` and
`PhysicalNormalInverse.OriginalTransport.geometry`
(`app:ch_waves:thm:sampling`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

open Set Metric
open scoped ContDiff

namespace JanetCartan.PhysicalSeed
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalConic
open CanonicalCarrier LeadingPrimitive FullPhaseCharts.ActualComparison
open LeadingWave.FullModulation NullTransport FlowAmplitude ActualFlow

/-- Original carrier-cell membership gives the actual incident root's open
leading, phase and comparison windows. No working radius or new parent is
chosen. The root remains distinct from the retained leading-cell center
(`app:ch_waves:thm:sampling`, `app:ch_waves:eq:joint-tame`). -/
theorem original_root_static_buffers {n : ℕ} (hn : 5 ≤ n)
    (q : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1))
    (j : OriginalBoundary.centers hn ⟨q.1.1, l⟩)
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)) :
    let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
    let zRoot := (OriginalBoundary.D hn).roots q.1.1 l q.1.2
    let zCell := j.1.1
    let graphRoot := ((0 : Euclidean n), (zRoot, T.reference.spatialPatch zRoot))
    graphRoot ∈ ball ((0 : Euclidean n), (zCell, T.reference.spatialPatch zCell))
        (OriginalBoundary.σcover hn ⟨q.1.1, l⟩ j) ∧
      graphRoot ∈ domain T ∧
      ((0 : ℝ), ((0 : Euclidean (n - 1)), zRoot)) ∈
        Ioo (-OriginalBoundary.δcomp hn ⟨q.1.1, l⟩ j)
          (OriginalBoundary.δcomp hn ⟨q.1.1, l⟩ j) ×ˢ
          ball ((0 : Euclidean (n - 1)), zCell) (OriginalBoundary.rcomp hn ⟨q.1.1, l⟩ j) ∧
      zRoot ∈ parameterInterior ((OriginalBoundary.D hn).patches q.1.1 l).radius := by
  intro T zRoot zCell graphRoot
  have hcell := OriginalBoundary.carrier_cells hn ⟨q.1.1, l⟩ j
  have hpoint : ((0 : Euclidean n), (zRoot 0, spectatorCenter zRoot)) ∈
      ball (0 : Euclidean n) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j) ×ˢ
        ball (zCell 0, spectatorCenter zCell) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j) :=
    ⟨mem_ball_self hcell.1, hroot⟩
  have hgraph := hcell.2.2.1 hpoint
  have hcoordinates := hcell.2.2.2.1 hpoint
  have hphysical := hcell.2.2.2.2.1 hpoint
  have hdouble : zRoot ∈ parameterInterior
      (2 * ((OriginalBoundary.D hn).patches q.1.1 l).radius) := by
    simpa only [mem_preimage, parameter_apply, carrierParameters_spectatorCenter] using hphysical.2
  have hphase : graphRoot ∈ domain T := by
    change (0, T.reference.spatialPatch zRoot) ∈ phaseDomain T
    exact carrier_mem_phaseDomain T hphysical.1.2 (fun i ↦ (hdouble i).le)
  have hzRoot : zRoot ∈ parameterInterior ((OriginalBoundary.D hn).patches q.1.1 l).radius :=
    (((OriginalBoundary.hD hn).2.2.2.2.1 q.1.1 l).2.2.1 q.1.2 q.2.2).1
  refine ⟨?_, hphase, ?_, hzRoot⟩
  · simpa only [carrierGraph, parameter_apply, carrierParameters_spectatorCenter] using hgraph
  · simpa only [parameter_apply, carrierParameters_spectatorCenter, coordinates_apply,
      map_zero, Prod.fst_zero, Prod.snd_zero] using hcoordinates

variable {n : ℕ} (hn : 5 ≤ n) (εframe : ℝ) (hεframe : 0 < εframe)
  (qext : BallExtension.Parameters (Euclidean n))
  (hqcenter : qext.center = 0) (hqradius : qext.radius = OriginalBoundary.b hn)
  (k : (a : Fin (OriginalBoundary.D hn).chartCount) ×
    Fin ((OriginalBoundary.D hn).patchCount a) → Euclidean n)
  (hk : ∀ a, k a ≠ 0) (hkD : ∀ a, k a ∈ (OriginalBoundary.D hn).domain a.1)
  (p : BallExtension.Parameters (Euclidean n)) (orders : Finset ℕ)
  (margin extendedMargin : ℕ → ℝ)
  (hmargin : ∀ a ∈ orders, 0 < margin a)
  (hextendedMargin : ∀ a ∈ orders, 0 < extendedMargin a)
  (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hincidenceCap : 0 < incidenceCap)
  (aExtra : (q : IncidenceCenter (OriginalBoundary.D hn)) →
    (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1)) →
      OriginalBoundary.centers hn ⟨q.1.1, l⟩ → {ε : ℝ // 0 < ε})

local notation "selectedCell" => SelectedBoundary.cell hn εframe hεframe qext hqcenter hqradius
  k hk hkD p orders margin extendedMargin hmargin hextendedMargin cap hcap
  incidenceCap hincidenceCap aExtra

/-- The same original 21 inputs give the actual root buffers on their already
selected parent. This only projects `fact1`; no radius, finite initializer or
leading-flow witness is selected (`new:sec:order-of-choices`). -/
theorem selected_root_static_buffers
    (q : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1)) :
    let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
    let zRoot := (OriginalBoundary.D hn).roots q.1.1 l q.1.2
    let j := selectedCell q l
    let zCell := j.1.1
    let graphRoot := ((0 : Euclidean n), (zRoot, T.reference.spatialPatch zRoot))
    graphRoot ∈ ball ((0 : Euclidean n), (zCell, T.reference.spatialPatch zCell))
        (OriginalBoundary.σcover hn ⟨q.1.1, l⟩ j) ∧
      graphRoot ∈ domain T ∧
      ((0 : ℝ), ((0 : Euclidean (n - 1)), zRoot)) ∈
        Ioo (-OriginalBoundary.δcomp hn ⟨q.1.1, l⟩ j)
          (OriginalBoundary.δcomp hn ⟨q.1.1, l⟩ j) ×ˢ
          ball ((0 : Euclidean (n - 1)), zCell) (OriginalBoundary.rcomp hn ⟨q.1.1, l⟩ j) ∧
      zRoot ∈ parameterInterior ((OriginalBoundary.D hn).patches q.1.1 l).radius := by
  exact original_root_static_buffers hn q l (selectedCell q l)
    (SelectedBoundary.fact1 hn εframe hεframe qext hqcenter hqradius k hk hkD p orders
      margin extendedMargin hmargin hextendedMargin cap hcap incidenceCap hincidenceCap aExtra q l).2

end JanetCartan.PhysicalSeed
