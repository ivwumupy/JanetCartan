module

public import JanetCartan.Iteration.PhysicalSampling.OnWorkingRadius
public import JanetCartan.Iteration.PhysicalSampling.OriginalWorkingRadius
public import JanetCartan.Iteration.PhysicalNormalInverse.TransportGeometry

/-!
# Actual original scalar geometry on the common pre-source radius

The concrete original root, parent, quarter direction and named working radius
supply every static argument of the original scalar sharp/continuum producer.
The actual original spatial/angular cap admission and the shared measured event
still have to be applied to this same data. This is not an assumed scalar norm
bound or a completed sampled row (`new:eq:amplitude-test`, Step 1,
`app:ch_waves:thm:sampling`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

open Set Metric
namespace JanetCartan.PhysicalSampling.OriginalScalar
open PhysicalSeed ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalConic
open FullPhaseCharts.ActualComparison

-- The exact proved continuation is retained without manually reconstructing
-- its operators or dependent proof arguments.
set_option quotPrecheck false in
local notation "originalScalarGeometryProof(" hn ", " q ", " l ", " j ", " hroot ")" =>
  (let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
   let hP := ((OriginalBoundary.hD hn).2.2.2.2.1 q.1.1 l).1
   let hz := (original_root_static_buffers hn q l j hroot).2.2.2
   let facts := PhysicalNormalInverse.OriginalTransport.quarter_incidence_facts hn q l
   let ρ := originalSamplingRadius hn q l j
   let buffers := originalSamplingRadius_spec hn q l j hroot
   exists_original_scalar_sampling_bounds_on_workingRadius
     (Nat.le_trans (by decide : 2 ≤ 5) hn) T hP hz facts.1 facts.2.1 facts.2.2.1
     ρ.2 buffers.2.2.2.1 buffers.2.1 buffers.2.2.2.2.1
     (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1))

/-- Actual original scalar geometry and its full sharp/continuum continuation,
on precisely the one original radius before reference or source scale. -/
theorem exists_geometry {m : ℕ} (hn : 5 ≤ m + 1)
    (q : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1))
    (j : OriginalBoundary.centers hn ⟨q.1.1, l⟩)
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)) :
    type_of% (originalScalarGeometryProof(hn, q, l, j, hroot)) :=
  originalScalarGeometryProof(hn, q, l, j, hroot)

end JanetCartan.PhysicalSampling.OriginalScalar
