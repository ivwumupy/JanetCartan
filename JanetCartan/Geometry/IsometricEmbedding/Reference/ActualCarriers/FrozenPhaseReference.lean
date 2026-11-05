module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.AdaptedSectionConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.DecoratedCover
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.NeighborhoodConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.PatchRefinement
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.ReferenceProperties

/-!
# Frozen patches retaining their Hamilton reference charts

Unconditional finite reference construction for
`app:ch_seed:prop:seed-frozen-menu` and Steps 1–2 of
`app:ch_seed:prop:seed-actual-menu`. Starting from `5 ≤ n`, the construction
chooses adapted sections and actual local Hamilton charts, shrinks the
characteristic graphs inside their covector neighborhoods, and only then
constructs incidence sections and the finite detecting cover.

The decorations retain the doubled closed patch bounds and the same reference
chart's low-order perturbation family. Their references supply the `R` argument
of `exists_finite_carrierPhase_assembly`. Current full-phase comparison,
all-order continuity and conic extension remain separate obligations; none is
an assumption of the frozen reference existence theorems here.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.FrozenPhaseReference
open FrozenMenu

/-- After the local Hamilton construction, shrink the actual characteristic
graph once and retain its reference data on the doubled closed cube.
This produces patches before incidence sections are continued, so the latter
can be centered on the final parameter cube
(`app:ch_seed:prop:seed-frozen-menu`, Steps 3–4;
`app:ch_seed:prop:seed-actual-menu`, Steps 1–2).
The local reference input is discharged by `exists_frozenPatchData_of_carrierSeed`
below. -/
theorem exists_frozenPatchData_of_localReference {n : ℕ} (hn : 5 ≤ n)
    {k s ξ : Euclidean n} (hseed : CarrierSeed k s ξ)
    (a : AdaptedSection ξ) (N : LocalFrozenReference a) :
    ∃ (P : Patch n) (c C : ℝ), P.IsValid c C ∧ P.toFun 0 = ξ ∧
      (∀ z ∈ parameterCube P.radius,
        c ≤ |fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z (EuclideanSpace.single 0 1)|) ∧
      Nonempty (FrozenPatchData P) := by
  obtain ⟨P, c, C, hP, hcenter, hinc, hbuffer⟩ :=
    exists_valid_patch_in_open hn hseed N.covectorSet_open N.covectorSet_base
  exact ⟨P, c, C, hP, hcenter, hinc,
    ⟨⟨ξ, a, N, hcenter, fun z hz ↦ (hbuffer z hz).1,
      fun z hz ↦ (hbuffer z hz).2.1, c, C, hP.2.1,
      fun z hz ↦ (hbuffer z hz).2.2.2⟩⟩⟩

/-- Construct a frozen patch and its actual Hamilton reference directly from
a detecting seed. All local analytic inputs are discharged before shrinking;
the incidence derivative survives on the final cube
(`app:ch_seed:prop:seed-frozen-menu`, Steps 3–4;
`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem exists_frozenPatchData_of_carrierSeed {n : ℕ} (hn : 5 ≤ n)
    {k s ξ : Euclidean n} (hseed : CarrierSeed k s ξ) :
    ∃ (P : Patch n) (c C : ℝ), P.IsValid c C ∧ P.toFun 0 = ξ ∧
      (∀ z ∈ parameterCube P.radius,
        c ≤ |fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z (EuclideanSpace.single 0 1)|) ∧
      Nonempty (FrozenPatchData P) := by
  obtain ⟨a⟩ := exists_adaptedSection_of_carrierSeed hn hseed
  have hξ : ξ ≠ 0 := by
    intro hzero
    exact hseed.coordinates_ne_zero ⟨0, by omega⟩ (by simp [hzero])
  obtain ⟨N⟩ := exists_localFrozenReference hξ hseed.characteristic a
  exact exists_frozenPatchData_of_localReference hn hseed a N

/-- The finite frozen detecting menu with constructed Hamilton data on every
literal patch index. Only the dimension hypothesis is required. Each output
`FrozenPatchData` retains its adapted unit normal and orthogonal section,
doubled closed characteristic patch and annulus, positive determinant gap,
affine full-phase identity, physical/section buffers, and the same chart's
fixed-state C³ perturbation family. Incidence sections are reconstructed after
the final shrinking and the full image-channel detector is preserved
(`app:ch_seed:prop:seed-frozen-menu`, Steps 3–4;
`app:ch_seed:prop:seed-actual-menu`, Steps 1–2;
`app:lem:common-hamilton-phase`). -/
theorem exists_frozenReference_coverData {n : ℕ} (hn : 5 ≤ n) :
    ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      Nonempty ((b : Fin D.chartCount) → (a : Fin (D.patchCount b)) →
        FrozenPatchData (D.patches b a)) := by
  obtain ⟨D, c, C, hD, hd⟩ := exists_decorated_coverData_of_local_patches hn
    FrozenPatchData (fun _ _ _ hseed ↦ exists_frozenPatchData_of_carrierSeed hn hseed)
  exact ⟨D, c, C, hD, ⟨fun b a ↦ Classical.choice (hd b a)⟩⟩

/-- The unconditional reference argument in the exact dependent-index form
consumed by `exists_finite_carrierPhase_assembly`. The accompanying decorations
identify each reference with the very chart whose state buffer, central
equivalence, positive C³ threshold and perturbation family were constructed;
they do not assert existence of current full-phase comparison estimates
(`app:ch_seed:prop:seed-actual-menu`, Steps 1–2). -/
theorem exists_finite_frozenPhaseReference {n : ℕ} (hn : 5 ≤ n) :
    ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ (R : (a : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
        CarrierPhaseReference (D.patches a.1 a.2)),
        (∀ a, (R a).symbol = normalizedHomogeneousSymbol isOpen_univ
          (fun _ : Euclidean n ↦ cubeStress n) contDiffOn_const) ∧
        ∃ d : (a : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
          FrozenPatchData (D.patches a.1 a.2), ∀ a, (d a).reference = R a := by
  obtain ⟨D, c, C, hD, ⟨d⟩⟩ := exists_frozenReference_coverData hn
  exact ⟨D, c, C, hD, fun a ↦ (d a.1 a.2).reference,
    fun a ↦ (d a.1 a.2).reference_symbol_eq, fun a ↦ d a.1 a.2, fun _ ↦ rfl⟩

end JanetCartan.ActualCarriers.FrozenPhaseReference
