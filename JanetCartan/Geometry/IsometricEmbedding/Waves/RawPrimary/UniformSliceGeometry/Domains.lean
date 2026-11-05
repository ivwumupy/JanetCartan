module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.Domains

/-!
# Common physical and covector buffers for the entire carrier cube

The maximum covector distance is taken on the original compact cube before
selecting the radii. These are the original domains consumed by
`exists_uniform_canonicalSliceNormalData`; no carrier labels are discarded.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.UniformSliceGeometry
open SliceGeometry ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts.ActualPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Common radii on every original carrier label, with arbitrary positive
physical and covector caps. The source-radius buffer is retained as well as
the full-phase radius. Consumed by `exists_uniform_canonicalSliceNormalData`
(`app:ch_waves:setup:oscillatory`, `app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_uniform_slice_domain_radii {c C : ℝ} (hP : P.IsValid c C)
    {amax bmax : ℝ} (ha : 0 < amax) (hb : 0 < bmax) :
    ∃ a₀ > (0 : ℝ), 4 * a₀ ≤ amax ∧ 4 * a₀ < T.family.radius ∧
      ∃ b > (0 : ℝ), b ≤ bmax ∧
        (∀ z ∈ parameterCube P.radius,
          ball (T.reference.spatialPatch z) b ⊆
            ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius))) ∧
        ∃ e₀ > (0 : ℝ), 16 * e₀ < b := by
  have hsub : parameterCube P.radius ⊆ parameterInterior (2 * P.radius) := by
    intro z hz i
    exact (hz i).trans_lt (by linarith [hP.1])
  have hc : ContinuousOn (fun z ↦ dist (T.reference.spatialPatch z) (covectorCenter T))
      (parameterCube P.radius) := by
    change ContinuousOn (fun z ↦ ‖T.reference.spatialPatch z - covectorCenter T‖) _
    exact (((T.reference.spatialPatch_smooth hP).continuousOn.mono hsub).sub
      continuousOn_const).norm
  obtain ⟨z₀, hz₀, hmax⟩ := (isCompact_parameterCube P.radius).exists_isMaxOn
    ⟨0, zero_mem_parameterCube hP.1.le⟩ hc
  let a₀ := min (amax / 4) (T.family.radius / 8)
  have ha₀ : 0 < a₀ := lt_min (by positivity) (by have := T.family.radius_pos; positivity)
  have hz' := mem_ball.mp (spatialPatch_mem_initial_covector_ball T
    (fun i ↦ (hsub hz₀ i).le))
  let R := min T.family.radius (3 * T.family.sourceRadius)
  let d := dist (T.reference.spatialPatch z₀) (covectorCenter T)
  let b := min bmax ((R - d) / 2)
  have hb' : 0 < b := lt_min hb (by dsimp [R, d]; linarith)
  refine ⟨a₀, ha₀, ?_, ?_, b, hb', min_le_left _ _, ?_, b / 32, by positivity, ?_⟩
  · have := min_le_left (amax / 4) (T.family.radius / 8)
    dsimp only [a₀]; linarith
  · have := min_le_right (amax / 4) (T.family.radius / 8)
    dsimp only [a₀]; linarith [T.family.radius_pos]
  · intro z hz η hη
    have hh := dist_triangle η (T.reference.spatialPatch z) (covectorCenter T)
    have hη' := mem_ball.mp hη
    have hbr : b ≤ (R - d) / 2 := min_le_right _ _
    have hzd : dist (T.reference.spatialPatch z) (covectorCenter T) ≤ d := hmax hz
    change dist η (covectorCenter T) < R
    change d < R at hz'
    linarith
  · linarith

end JanetCartan.RawPrimary.UniformSliceGeometry
