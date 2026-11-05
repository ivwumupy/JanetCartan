module

public import JanetCartan.Iteration.PhysicalSampling.MeasuredMean
public import JanetCartan.Iteration.PhysicalSampling.OriginalWorkingRadius
public import JanetCartan.Iteration.PhysicalNormalInverse.TransportGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedBandBounds

/-!
# Original measured geometry before the source-dependent budgets

Specialize both proved corrected-band and measured-mean factories to the
literal original root and the ONE named working radius. The quarter covector
is the same as the original selector's normalization. The returned geometric
constants precede every immersion bound, gap, coefficient profile and current
field. The later actual-profile and common-event application is not claimed
here (`app:ch_waves:eq:sampling-operator-bounds`,
`app:ch_waves:eq:colored-normal-comparison`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open Set Metric
namespace JanetCartan.PhysicalSampling.OriginalMeasured
open PhysicalSeed ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalConic
open Sampling FullPhaseCharts FullPhaseCharts.ActualComparison LeadingWave.FullModulation

-- Explicit syntax arguments retain the exact type of the existing proved
-- factory; only the eager notation precheck for its local lets is bypassed.
set_option quotPrecheck false in
local notation "originalMeasuredGeometryProof(" p ", " hn ", " q ", " l ", " j ", " hroot ")" =>
  (let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
   let hP := ((OriginalBoundary.hD hn).2.2.2.2.1 q.1.1 l).1
   let hz := (original_root_static_buffers hn q l j hroot).2.2.2
   let facts := PhysicalNormalInverse.OriginalTransport.quarter_incidence_facts hn q l
   let ρ := originalSamplingRadius hn q l j
   let buffers := originalSamplingRadius_spec hn q l j hroot
   let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint ((1 / 4 : ℝ) • q.1.2)
   let hηnorm : 0 < ‖ηb‖ := norm_pos_iff.mpr facts.2.2.2
   let hamin : 0 < (1 / 2 : ℝ) / ‖ηb‖ := div_pos (by norm_num) hηnorm
   let hamax : (1 / 2 : ℝ) / ‖ηb‖ ≤ 2 / ‖ηb‖ :=
     div_le_div_of_nonneg_right (by norm_num) hηnorm.le
   exists_corrected_mean_geometry_before_immersion_budgets
     (p := p) (rmax := 1) (emax := 1) (xmax := 1)
     T hP hz facts.1 facts.2.1 facts.2.2.1 ρ.2
     (by norm_num) (by norm_num) (by norm_num) hamin hamax
     buffers.2.2.2.1 buffers.2.1)

/-- The original quarter incidence and the shared original working radius
close every static measured-mean geometry input before source scale. -/
theorem exists_mean_geometry {m p : ℕ} (hn : 5 ≤ m + 1)
    (q : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1))
    (j : OriginalBoundary.centers hn ⟨q.1.1, l⟩)
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)) :
    type_of% (originalMeasuredGeometryProof(p, hn, q, l, j, hroot)) :=
  originalMeasuredGeometryProof(p, hn, q, l, j, hroot)

set_option quotPrecheck false in
local notation "originalBandGeometryProof(" m ", " hn ", " q ", " l ", " j ")" =>
  (let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
   let hP := ((OriginalBoundary.hD hn).2.2.2.2.1 q.1.1 l).1
   let zRoot := (OriginalBoundary.D hn).roots q.1.1 l q.1.2
   let ρ := originalSamplingRadius hn q l j
   Sampling.exists_uniform_correctedColoredCrossBand_bound_before_immersion_bounds
     (d := m) (by omega) hP T zRoot (T.reference.spatialPatch zRoot) ρ.2)

/-- Original corrected sharp-band geometry on the SAME named radius. The
phase-ball certificate in its retained analytic continuation is supplied by
`originalSamplingRadius_spec` on the actual selected parent. -/
theorem exists_band_geometry {m : ℕ} (hn : 5 ≤ m + 1)
    (q : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1))
    (j : OriginalBoundary.centers hn ⟨q.1.1, l⟩) :
    type_of% (originalBandGeometryProof(m, hn, q, l, j)) :=
  originalBandGeometryProof(m, hn, q, l, j)

end JanetCartan.PhysicalSampling.OriginalMeasured
