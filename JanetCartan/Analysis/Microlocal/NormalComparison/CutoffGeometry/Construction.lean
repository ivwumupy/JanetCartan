module

public import JanetCartan.Analysis.Microlocal.NormalComparison.CutoffGeometry.Buffer
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# Fixed scalar cutoff geometry

The rank-one geometry and cutoffs used in Step 2 of
`app:ch_osc:prop:osc-normal`. All choices precede the phase family.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.NormalComparison

variable {n r : ℕ}

/-- The rank-one geometry of the scalar channel in
`app:ch_osc:prop:osc-normal`, with the original open boxes and determinant gap.
The compact supports are enlarged, and the three positive buffers are halved. -/
def UniformNormalGeometry.scalarCutoffGeometry (G : UniformNormalGeometry n r)
    (C : ℕ → ℝ) : UniformNormalGeometry n 1 where
  dimension_pos := G.dimension_pos
  rank_pos := le_rfl
  X := G.X
  D := G.D
  X₀ := cthickening (G.spatialBuffer / 2) G.X₀
  D₀ := cthickening (G.cutoffInputRadius C) G.D₀
  V := G.V
  isOpen_X := G.isOpen_X
  isOpen_D := G.isOpen_D
  convex_X := G.convex_X
  convex_D := G.convex_D
  bounded_X := G.bounded_X
  bounded_D := G.bounded_D
  compact_X₀ := G.compact_X₀.cthickening
  compact_D₀ := G.compact_D₀.cthickening
  isOpen_V := G.isOpen_V
  compact_closure_V := G.compact_closure_V
  ε₀ := G.ε₀
  spatialBuffer := G.spatialBuffer / 2
  inputBuffer := G.inputBuffer / 2
  inverseBuffer := G.inverseBuffer / 2
  gap := G.gap
  ε₀_pos := G.ε₀_pos
  spatialBuffer_pos := half_pos G.spatialBuffer_pos
  inputBuffer_pos := half_pos G.inputBuffer_pos
  inverseBuffer_pos := half_pos G.inverseBuffer_pos
  gap_pos := G.gap_pos
  spatial_buffer := by
    apply (cthickening_cthickening_subset (half_pos G.spatialBuffer_pos).le
      (half_pos G.spatialBuffer_pos).le _).trans
    simpa only [add_halves] using G.spatial_buffer
  input_buffer := G.cutoff_input_buffer C

/-- A pair of actual smooth scalar cutoffs for Step 2 of
`app:ch_osc:prop:osc-normal`. The producer `fixedScalarNormalCutoffs` below
constructs all fields using only the fixed geometry and original jet budget. -/
structure ScalarNormalCutoffs (G : UniformNormalGeometry n r) (C : ℕ → ℝ) where
  χx : Euclidean n → ℝ
  χu : Euclidean n → ℝ
  smooth_x : ContDiff ℝ ∞ χx
  smooth_u : ContDiff ℝ ∞ χu
  range_x : ∀ x, χx x ∈ Icc (0 : ℝ) 1
  range_u : ∀ u, χu u ∈ Icc (0 : ℝ) 1
  compact_x : HasCompactSupport χx
  compact_u : HasCompactSupport χu
  support_x : tsupport χx ⊆ (G.scalarCutoffGeometry C).X₀
  support_u : tsupport χu ⊆ (G.scalarCutoffGeometry C).D₀
  plateau_x : G.X₀ ⊆ interior {x | χx x = 1}
  plateau_u : G.D₀ ⊆ interior {u | χu u = 1}

/-- The fixed pair required by `app:ch_osc:prop:osc-normal`, Step 2, exists
without assumptions on an individual phase family. -/
theorem nonempty_scalarNormalCutoffs (G : UniformNormalGeometry n r) (C : ℕ → ℝ) :
    Nonempty (ScalarNormalCutoffs G C) := by
  obtain ⟨χx, hsx, hrx, hcx, htx, hpx⟩ := CompatibleResponse.exists_compact_family_cutoff
    G.compact_X₀ isOpen_thickening
    (self_subset_thickening (half_pos G.spatialBuffer_pos) G.X₀)
  obtain ⟨χu, hsu, hru, hcu, htu, hpu⟩ := CompatibleResponse.exists_compact_family_cutoff
    G.compact_D₀ isOpen_thickening
    (self_subset_thickening (G.cutoffInputRadius_pos C) G.D₀)
  exact ⟨⟨χx, χu, hsx, hsu, hrx, hru, hcx, hcu,
    htx.trans (thickening_subset_cthickening _ _),
    htu.trans (thickening_subset_cthickening _ _), hpx, hpu⟩⟩

/-- One cutoff choice for `app:ch_osc:prop:osc-normal`, Step 2, independent
of the family, frequency, parameter and mask. -/
def fixedScalarNormalCutoffs (G : UniformNormalGeometry n r) (C : ℕ → ℝ) :
    ScalarNormalCutoffs G C := Classical.choice (nonempty_scalarNormalCutoffs G C)

variable {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- The spatial cutoff is compactly supported inside the original open box
(`app:ch_osc:prop:osc-normal`). -/
theorem ScalarNormalCutoffs.tsupport_x_subset (χ : ScalarNormalCutoffs G C) :
    tsupport χ.χx ⊆ G.X := χ.support_x.trans (G.scalarCutoffGeometry C).X₀_subset

/-- The input cutoff is compactly supported inside the original open box
(`app:ch_osc:prop:osc-normal`). -/
theorem ScalarNormalCutoffs.tsupport_u_subset (χ : ScalarNormalCutoffs G C) :
    tsupport χ.χu ⊆ G.D := χ.support_u.trans (G.scalarCutoffGeometry C).D₀_subset

end JanetCartan.NormalComparison
