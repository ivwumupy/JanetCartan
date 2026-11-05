module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Cover
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.RadialGap
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.LocalPatches.CubeGeometry

/-!
# Separation for the constructed frozen menu

The final assembly in `app:ch_seed:prop:seed-frozen-menu`: projected chords
separate all distinct parameters, and radial labels work uniformly for every
patch in each color group. Repeated patch specifications remain separate.
-/

@[expose] public noncomputable section

namespace JanetCartan.FrozenMenu

/-- The reciprocal quadratic vector is a nonzero characteristic normal on
every valid patch (`app:ch_seed:prop:seed-frozen-menu`, item 1). -/
theorem Patch.IsValid.characteristic_normal {n : ℕ} {P : Patch n} {c C : ℝ}
    (hP : P.IsValid c C) {z : Euclidean 3} (hz : z ∈ parameterCube P.radius) :
    normal (P.toFun z) ≠ 0 ∧ fderiv ℝ cubeDeterminant (P.toFun z) ≠ 0 ∧
      ∃ t : ℝ, t ≠ 0 ∧ fderiv ℝ cubeDeterminant (P.toFun z) =
        t • innerSL ℝ (normal (P.toFun z)) := by
  obtain ⟨hcoord, hchar, _, hn, _⟩ := hP.2.2.2.2.1 z hz
  exact ⟨hn, CubeCarrier.regular_of_quadratic_reciprocal_ne_zero hcoord hchar hn,
    _, CubeCarrier.determinant_normal_multiplier_ne_zero hcoord hchar,
    CubeCarrier.determinant_differential_eq_innerSL hcoord hchar⟩

/-- The projected chord bound separates every pair of distinct parameters,
including arbitrarily short chords (`app:ch_seed:prop:seed-frozen-menu`, item 1,
and `app:ch_seed:eq:seed-frozen-chord`). -/
theorem Patch.IsValid.chord_separation {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {z w : Euclidean 3} (hz : z ∈ parameterCube P.radius)
    (hw : w ∈ parameterCube P.radius) (hzw : z ≠ w) :
    P.toFun z - P.toFun w ≠ 0 ∧
      BadDirectionGap (c / C) (P.toFun z - P.toFun w) := by
  have hd : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  obtain ⟨hlower, hupper, _⟩ := hP.2.2.2.2.2 z hz w hw
  obtain ⟨L, hL, _⟩ := Set.mem_iUnion₂.mp (zero_mem_cubeBadSubspaceUnion hn)
  refine ⟨norm_pos_iff.mp ?_,
    badDirectionGap_of_chord_bounds hd hP.2.1 hP.2.2.1 hlower hupper⟩
  exact (mul_pos hP.2.1 hd).trans_le ((hlower L hL).trans
    (Lᗮ.norm_orthogonalProjectionOnto_apply_le _))

/-- Positive fixed labels preserve normalized directional gaps
(`app:ch_seed:prop:seed-frozen-menu`, item 3). -/
theorem BadDirectionGap.smul_pos {n : ℕ} {x : Euclidean n} {δ R : ℝ}
    (h : BadDirectionGap δ x) (hR : 0 < R) : BadDirectionGap δ (R • x) := by
  simpa only [BadDirectionGap, NormedSpace.normalize_smul_of_pos hR] using h

/-- Within one patch and group, radial scaling preserves separation of
differences and sums (`app:ch_seed:prop:seed-frozen-menu`, item 3). -/
theorem Patch.IsValid.scaled_pair_separation {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c C R : ℝ} (hP : P.IsValid c C) (hR : 0 < R)
    {z w : Euclidean 3} (hz : z ∈ parameterCube P.radius)
    (hw : w ∈ parameterCube P.radius) :
    (z ≠ w → R • P.toFun z - R • P.toFun w ≠ 0 ∧
      BadDirectionGap (c / C) (R • P.toFun z - R • P.toFun w)) ∧
    R • P.toFun z + R • P.toFun w ≠ 0 ∧
      BadDirectionGap c (R • P.toFun z + R • P.toFun w) := by
  obtain ⟨_, _, hsum, hgap⟩ := hP.2.2.2.2.2 z hz w hw
  rw [← smul_sub, ← smul_add]
  refine ⟨fun hzw ↦ ?_, smul_ne_zero hR.ne' hsum, hgap.smul_pos hR⟩
  obtain ⟨hne, hd⟩ := hP.chord_separation hn hz hw hzw
  exact ⟨smul_ne_zero hR.ne' hne, hd.smul_pos hR⟩

/-- The radial-label conclusion of `app:ch_seed:prop:seed-frozen-menu`, item 3.
Every patch is allowed in every group, so this covers any grouping and any
number of duplicate specifications. There is no sampling parameter. This is
a conclusion to be proved, not an input to the menu construction. -/
def CoverData.HasRadialSeparation {n : ℕ} (D : CoverData n) (G : Type*) (δ : ℝ) : Prop :=
  ∃ R : G → ℝ, (∀ g, 1 ≤ R g) ∧ Function.Injective R ∧
    ∀ g h, g ≠ h → ∀ b a b' a',
      ∀ z ∈ parameterCube (D.patches b a).radius,
      ∀ w ∈ parameterCube (D.patches b' a').radius,
        R g • (D.patches b a).toFun z - R h • (D.patches b' a').toFun w ≠ 0 ∧
        BadDirectionGap δ
          (R g • (D.patches b a).toFun z - R h • (D.patches b' a').toFun w) ∧
        R g • (D.patches b a).toFun z + R h • (D.patches b' a').toFun w ≠ 0 ∧
        BadDirectionGap δ
          (R g • (D.patches b a).toFun z + R h • (D.patches b' a').toFun w)

/-- Apply radial domination to all points of all constructed patches at once.
The common norm and regularity bounds discharge every geometric premise of
the radial-label theorem (`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
theorem CoverData.IsValid.hasRadialSeparation {n : ℕ} {D : CoverData n} {c C : ℝ}
    (hD : D.IsValid c C) (G : Type*) [Finite G] :
    D.HasRadialSeparation G (c / 2) := by
  let Z := (b : Fin D.chartCount) × (a : Fin (D.patchCount b)) ×
    {z : Euclidean 3 // z ∈ parameterCube (D.patches b a).radius}
  let ξ : G → Z → Euclidean n := fun _ p ↦ (D.patches p.1 p.2.1).toFun p.2.2.1
  have hpoint (p : Z) := (hD.2.2.2.2.1 p.1 p.2.1).1.2.2.2.2.1 p.2.2.1 p.2.2.2
  obtain ⟨R, hR, hinj, hsep⟩ := exists_radial_badDirectionGap ξ hD.1 hD.2.1.le hD.1
    (fun _ p ↦ ⟨(hpoint p).2.2.2.2.1, (hpoint p).2.2.2.2.2.1⟩)
    (fun _ p ↦ (hpoint p).2.2.2.2.2.2)
  refine ⟨R, hR, hinj, ?_⟩
  intro g h hgh b a b' a' z hz w hw
  exact hsep g h hgh ⟨b, a, z, hz⟩ ⟨b', a', w, hw⟩

end JanetCartan.FrozenMenu
