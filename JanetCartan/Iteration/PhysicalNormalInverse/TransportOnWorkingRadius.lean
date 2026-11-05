module

public import JanetCartan.Iteration.PhysicalNormalInverse.TransportGeometry
public import JanetCartan.Iteration.PhysicalSampling.OriginalWorkingRadius

/-!
# Original transport geometry on the ONE named pre-source working radius

This applies the actual quarter-normalized transport constructor to the literal
`PhysicalSampling.originalSamplingRadius`, including its original parent cell.
No radius, source initializer, current row, phase or cutoff is chosen here.
The admitted-parent premise is the exact second projection of the selected
initializer's `fact1`, with the SAME capped callback (`new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16000
open Set Metric
namespace JanetCartan.PhysicalNormalInverse.OriginalTransport
open PhysicalSeed ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalConic
open FullPhaseCharts.ActualComparison PhysicalSampling

/-- Close every working-radius input on the literal common pre-source choice.
The resulting buffers still precede all immersion/gap/profile budgets. The
original incident root, quarter-scaled covector and leading-cell index remain
unchanged (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem geometry_on_originalSamplingRadius {m p : ℕ} (hn : 5 ≤ m + 1)
    (q : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1))
    (j : OriginalBoundary.centers hn ⟨q.1.1, l⟩)
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)) :
    type_of% (geometry (p := p) hn q l (originalSamplingRadius hn q l j).property
      (originalSamplingRadius_spec hn q l j hroot).2.2.2.1
      (originalSamplingRadius_spec hn q l j hroot).2.1) :=
  geometry (p := p) hn q l (originalSamplingRadius hn q l j).property
      (originalSamplingRadius_spec hn q l j hroot).2.2.2.1
      (originalSamplingRadius_spec hn q l j hroot).2.1

end JanetCartan.PhysicalNormalInverse.OriginalTransport
