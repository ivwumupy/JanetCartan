module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.TangentFrames
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.ChordEstimates
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.LocalPatches.CubeGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.LocalPatches.UniformBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.LocalPatches.CharacteristicGraph
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.LocalPatches.Shrinking

/-!
# Local frozen characteristic patches

The construction in Step 3 of `app:ch_seed:prop:seed-frozen-menu`:
select an admissible tangent three-frame, construct its characteristic graph
by the implicit function theorem, and shrink to a closed convex parameter
cube satisfying all frozen-patch estimates.

The only pointwise geometric input is a carrier seed. In particular, neither
a chart nor any of its quantitative estimates is assumed.
-/

@[expose] public noncomputable section

namespace JanetCartan.FrozenMenu

/-- A carrier seed gives a smooth frozen characteristic patch centered at that
carrier, with every geometric estimate in `Patch.IsValid` and a uniform positive
first-parameter incidence derivative bound
(`app:ch_seed:prop:seed-frozen-menu`, Step 3, and
`app:ch_seed:eq:seed-frozen-chord`). The frame, implicit graph, and quantitative
shrinking are all constructed from the seed. -/
theorem CarrierSeed.exists_valid_patch {n : ℕ} (hn : 5 ≤ n)
    {k s ξ : Euclidean n} (h : CarrierSeed k s ξ) :
    ∃ (P : Patch n) (c C : ℝ), P.IsValid c C ∧ P.toFun 0 = ξ ∧
      ∀ z ∈ parameterCube P.radius,
        c ≤ |fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z (EuclideanSpace.single 0 1)| := by
  obtain ⟨A, hA⟩ := h.exists_admissibleFrame hn
  obtain ⟨e, u, U, hU, h0, _, _, _, _, hf, hf0, hdf0, hchar⟩ :=
    h.exists_characteristic_graph hn A hA
  obtain ⟨ρ, c, C, hP, hinc, _⟩ :=
    exists_valid_patch_of_characteristic_chart hn h hA hU h0 hf hf0 hdf0 hchar
  exact ⟨⟨ρ, fun z ↦ ξ + A z + u z • e⟩, c, C, hP, hf0, hinc⟩

end JanetCartan.FrozenMenu
