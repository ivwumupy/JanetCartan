module

public import JanetCartan.Iteration.PhysicalSampling.OriginalChoices
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedCutoffChoices
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.OriginalLabelCap

/-!
# One original joint cutoff and the sharp-band carrier cap

The cutoff is chosen from the SAME retained mean/comparison buffers and named
working radius. Its density-coordinate image lies in the original comparison
cell. A separate carrier-label cap places the unchanged original carrier
weight in the sharp-band graph ball. This latter cap does not choose another
working radius or change any kernel, original mask or external weight.

These are the concrete inputs to the pre-source `aExtra` minimum and the common
scalar/measured event (`new:sec:order-of-choices`,
`app:ch_waves:eq:sampling-operator-bounds`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open Set Metric
namespace JanetCartan.PhysicalSampling.OriginalCutoffs
open PhysicalSeed ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalConic
open FullPhaseCharts.ActualComparison Sampling OriginalChoices

set_option quotPrecheck false in
local notation "originalJointCutoffProof(" p ", " hn ", " q ", " l ", " j ", " hroot ")" =>
  (let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
   let hP := ((OriginalBoundary.hD hn).2.2.2.2.1 q.1.1 l).1
   let rootBuffers := original_root_static_buffers hn q l j hroot
   let ρ := originalSamplingRadius hn q l j
   let rJoint := min (Mean.radius (p := p) hn q l j hroot)
     (Comparison.radius (p := p) hn q l j hroot)
   let sJoint := min (Mean.s (p := p) hn q l j hroot)
     (Comparison.s (p := p) hn q l j hroot)
   let hrJoint : 0 < rJoint := lt_min (Mean.hradius (p := p) hn q l j hroot)
     (Comparison.hradius (p := p) hn q l j hroot)
   let hsJoint : 0 < sJoint := lt_min (Mean.hs (p := p) hn q l j hroot)
     (Comparison.hs (p := p) hn q l j hroot)
   exists_originalConic_corrected_sampling_cutoffs T hP rootBuffers.2.2.2 ρ.2 hrJoint hsJoint
     (Band.ha (p := p) hn q l j hroot) (isOpen_Ioo.prod isOpen_ball) rootBuffers.2.2.1)

/-- Choose the single auxiliary joint amplitude and carrier cutoff. The
physical band core is `Band.a`, while the carrier graph uses `Band.b` below. -/
theorem exists_joint_cutoff_geometry {m p : ℕ} (hn : 5 ≤ m + 1)
    (q : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1))
    (j : OriginalBoundary.centers hn ⟨q.1.1, l⟩)
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)) :
    type_of% (originalJointCutoffProof(p, hn, q, l, j, hroot)) :=
  originalJointCutoffProof(p, hn, q, l, j, hroot)

set_option quotPrecheck false in
local notation "originalBandLabelProof(" p ", " hn ", " q ", " l ", " j ", " hroot ")" =>
  (let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
   let hP := ((OriginalBoundary.hD hn).2.2.2.2.1 q.1.1 l).1
   let hz := (original_root_static_buffers hn q l j hroot).2.2.2
   let htarget : 0 < 2 * Band.b (p := p) hn q l j hroot :=
     mul_pos (by norm_num) (Band.hb (p := p) hn q l j hroot)
   exists_originalConic_sampling_label_cap T hP hz htarget)

/-- A numeric carrier-label cap, not a second working-ball choice, puts every
smaller original carrier weight in the sharp graph window `Band.b / 2`. -/
theorem exists_original_label_geometry {m p : ℕ} (hn : 5 ≤ m + 1)
    (q : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1))
    (j : OriginalBoundary.centers hn ⟨q.1.1, l⟩)
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)) :
    type_of% (originalBandLabelProof(p, hn, q, l, j, hroot)) :=
  originalBandLabelProof(p, hn, q, l, j, hroot)

end JanetCartan.PhysicalSampling.OriginalCutoffs
