module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.LocalPatches

/-!
# Frozen patches inside a prescribed canonical neighborhood

The final shrinking in Step 1 of `app:ch_seed:prop:seed-actual-menu` is
performed before constructing incidence sections. The extra characteristic
assertions on the doubled closed cube come from the actual characteristic
graph, rather than from an abstract patch's inner-cube specification.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff

namespace JanetCartan.ActualCarriers.FrozenPhaseReference
open FrozenMenu

/-- Retain a prescribed open covector neighborhood in the quantitative patch
construction, including characteristicity, nonvanishing and annular bounds on
the doubled **closed** cube (`app:ch_seed:prop:seed-frozen-menu`, Step 3;
`app:ch_seed:prop:seed-actual-menu`, Step 1). The canonical reference constructor
supplies `V`; centered incidence sections must be constructed after this step. -/
theorem exists_valid_patch_in_open {n : ℕ} (hn : 5 ≤ n)
    {k s ξ : Euclidean n} (h : CarrierSeed k s ξ)
    {V : Set (Euclidean n)} (hV : IsOpen V) (hξV : ξ ∈ V) :
    ∃ (P : Patch n) (c C : ℝ), P.IsValid c C ∧ P.toFun 0 = ξ ∧
      (∀ z ∈ parameterCube P.radius,
        c ≤ |fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z (EuclideanSpace.single 0 1)|) ∧
      ∀ z ∈ parameterCube (2 * P.radius),
        P.toFun z ∈ V ∧ cubeDeterminant (P.toFun z) = 0 ∧ P.toFun z ≠ 0 ∧
          c ≤ ‖P.toFun z‖ ∧ ‖P.toFun z‖ ≤ C := by
  obtain ⟨A, hA⟩ := h.exists_admissibleFrame hn
  obtain ⟨e, u, U, hU, h0, _, _, _, _, hf, hf0, hdf0, hchar⟩ :=
    h.exists_characteristic_graph hn A hA
  let f := fun z ↦ ξ + A z + u z • e
  have hopen : IsOpen (U ∩ f ⁻¹' V) := hf.continuousOn.isOpen_inter_preimage hU hV
  have hbase : (0 : Euclidean 3) ∈ U ∩ f ⁻¹' V := ⟨h0, by change f 0 ∈ V; rw [show f 0 = ξ from hf0]; exact hξV⟩
  obtain ⟨ρ, c, C, hP, hinc, hsub⟩ :=
    exists_valid_patch_of_characteristic_chart hn h hA hopen hbase
      (hf.mono inter_subset_left) hf0 hdf0 (fun z hz ↦ hchar z hz.1)
  have hhalf : 0 < ρ / 2 := half_pos hP.1
  have hinner : parameterCube (ρ / 2) ⊆ parameterCube ρ := by
    intro z hz i
    exact (hz i).trans (by linarith [hP.1])
  have hsmooth : parameterInterior (2 * (ρ / 2)) ⊆ parameterInterior (2 * ρ) := by
    intro z hz i
    exact (hz i).trans_le (by linarith [hP.1])
  refine ⟨⟨ρ / 2, f⟩, c, C, ?_, hf0, fun z hz ↦ hinc z (hinner hz), ?_⟩
  · exact ⟨hhalf, hP.2.1, hP.2.2.1, hP.2.2.2.1.mono hsmooth,
      fun z hz ↦ hP.2.2.2.2.1 z (hinner hz),
      fun z hz w hw ↦ hP.2.2.2.2.2 z (hinner hz) w (hinner hw)⟩
  · intro z hz
    have hzρ : z ∈ parameterCube ρ := by
      have he : 2 * (ρ / 2) = ρ := by ring
      simpa only [Patch.radius, he] using hz
    have hzU := hsub (parameterCube_subset_doubledInterior hP.1 hzρ)
    obtain ⟨_, hzero, _, _, hlower, hupper, _⟩ := hP.2.2.2.2.1 z hzρ
    refine ⟨hzU.2, hzero, ?_, hlower, hupper⟩
    exact norm_pos_iff.mp (lt_of_lt_of_le hP.2.1 hlower)

end JanetCartan.ActualCarriers.FrozenPhaseReference
