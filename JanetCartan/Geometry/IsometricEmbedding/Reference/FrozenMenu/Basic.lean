module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Strata
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Shared specifications for the frozen characteristic patches

The local objects in `app:ch_seed:prop:seed-frozen-menu`, Steps 3–4.
These definitions specify the geometric construction; they do not assert that
patches, incidence sections, or a finite detecting cover exist.
-/

@[expose] public noncomputable section

namespace JanetCartan.FrozenMenu

open CubeCarrier
open scoped ContDiff

/-- The closed three-dimensional parameter cube of
`app:ch_seed:prop:seed-frozen-menu`. -/
def parameterCube (ρ : ℝ) : Set (Euclidean 3) := {z | ∀ i, |z i| ≤ ρ}

/-- The open parameter cube used for smoothness and interior incidence roots
in `app:ch_seed:prop:seed-frozen-menu`. -/
def parameterInterior (ρ : ℝ) : Set (Euclidean 3) := {z | ∀ i, |z i| < ρ}

/-- The reciprocal characteristic normal in
`app:ch_seed:prop:seed-frozen-menu`. -/
def normal {n : ℕ} (ξ : Euclidean n) : Euclidean n := quadratic (reciprocal ξ)

/-- Incidence with a covector, in carrier coordinates
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
def incidence {n : ℕ} (k ξ : Euclidean n) : ℝ := ∑ i, k i * normal ξ i

/-- A quantitative distance from every bad subspace on normalized directions
(`app:ch_seed:prop:seed-frozen-menu`). Orthogonal projection measures the
distance to a closed linear subspace. -/
def BadDirectionGap {n : ℕ} (δ : ℝ) (v : Euclidean n) : Prop :=
  ∀ L ∈ cubeBadSubspaces n,
    δ ≤ ‖Lᗮ.orthogonalProjectionOnto (NormedSpace.normalize v)‖

/-- The pointwise output of Steps 1–2 needed by Step 3 of
`app:ch_seed:prop:seed-frozen-menu`. No patch or finite menu is an input. -/
structure CarrierSeed {n : ℕ} (k s ξ : Euclidean n) : Prop where
  coordinates_ne_zero : ∀ i, ξ i ≠ 0
  characteristic : cubeDeterminant ξ = 0
  normal_ne_zero : normal ξ ≠ 0
  incident : incidence k ξ = 0
  detects : (∑ i, s i * quadratic ξ i) ≠ 0
  triple_witness : ∀ i j l : Fin n, ∃ x : Euclidean n,
    x i = 0 ∧ x j = 0 ∧ x l = 0 ∧ (∑ a, x a * normal ξ a) ≠ 0
  pair_sum_witness : ∀ i j : Fin n, ∃ x : Euclidean n,
    x i = 0 ∧ x j = 0 ∧ (∑ a, x a) = 0 ∧ (∑ a, x a * normal ξ a) ≠ 0
  transverse : ∃ e : Euclidean n, fderiv ℝ cubeDeterminant ξ e = 0 ∧
    fderiv ℝ (incidence k) ξ e ≠ 0

/-- A three-frame tangent to the characteristic hypersurface, transverse to
incidence in its first column, and injective after every bad-space projection
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
def IsAdmissibleFrame {n : ℕ} (k ξ : Euclidean n)
    (A : Euclidean 3 →L[ℝ] Euclidean n) : Prop :=
  (fderiv ℝ cubeDeterminant ξ).comp A = 0 ∧
  fderiv ℝ (incidence k) ξ (A (EuclideanSpace.single 0 1)) ≠ 0 ∧
  ∀ L ∈ cubeBadSubspaces n, Function.Injective (Lᗮ.orthogonalProjectionOnto.comp A)

/-- The map and radius of a frozen patch. Its geometric assertions are stated
separately in `Patch.IsValid` (`app:ch_seed:prop:seed-frozen-menu`). -/
structure Patch (n : ℕ) where
  radius : ℝ
  toFun : Euclidean 3 → Euclidean n

/-- The local geometric specification in item 1 of
`app:ch_seed:prop:seed-frozen-menu`, including the projected chord estimate
`app:ch_seed:eq:seed-frozen-chord`. Existence is a separate proof obligation. -/
def Patch.IsValid {n : ℕ} (P : Patch n) (c C : ℝ) : Prop :=
  0 < P.radius ∧ 0 < c ∧ 0 < C ∧
  ContDiffOn ℝ ∞ P.toFun (parameterInterior (2 * P.radius)) ∧
  (∀ z ∈ parameterCube P.radius,
    (∀ i, P.toFun z i ≠ 0) ∧ cubeDeterminant (P.toFun z) = 0 ∧
    (cubePencil (P.toFun z)).rank = n - 1 ∧ normal (P.toFun z) ≠ 0 ∧
    c ≤ ‖P.toFun z‖ ∧ ‖P.toFun z‖ ≤ C ∧ BadDirectionGap c (P.toFun z)) ∧
  (∀ z ∈ parameterCube P.radius, ∀ w ∈ parameterCube P.radius,
    (∀ L ∈ cubeBadSubspaces n,
      c * ‖z - w‖ ≤ ‖Lᗮ.orthogonalProjectionOnto (P.toFun z - P.toFun w)‖) ∧
    ‖P.toFun z - P.toFun w‖ ≤ C * ‖z - w‖ ∧
    P.toFun z + P.toFun w ≠ 0 ∧ BadDirectionGap c (P.toFun z + P.toFun w))

/-- A smooth interior incidence section, with the last two coordinates fixed
to zero and a uniform first-parameter derivative bound on the patch
(`app:ch_seed:prop:seed-frozen-menu`, item 2). -/
def Patch.IsIncidenceSection {n : ℕ} (P : Patch n) (U : Set (Euclidean n))
    (root : Euclidean n → Euclidean 3) (c : ℝ) : Prop :=
  ContDiffOn ℝ ∞ root U ∧
  (∀ k ∈ U, root k ∈ parameterInterior P.radius ∧
    root k 1 = 0 ∧ root k 2 = 0 ∧ incidence k (P.toFun (root k)) = 0) ∧
  (∀ k ∈ U, ∀ z ∈ parameterCube P.radius,
    c ≤ |fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z (EuclideanSpace.single 0 1)|)

/-- Checked nonexceptional pointwise selection, expressed in the shared seed
specification (`app:ch_seed:prop:seed-frozen-menu`, Steps 1 and 3). -/
theorem exists_carrierSeed_of_nonexceptional {n : ℕ} (hn : 5 ≤ n)
    {k s : Euclidean n} (hk : k ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hnode : n = 5 → ¬ ∃ a b : Fin n, a ≠ b ∧ ∃ t : ℝ, k = t • cubeVector a b) :
    ∃ ξ, CarrierSeed k s ξ := by
  obtain ⟨ξ, hcoord, hchar, _, _, _, _, _, _, hnormal, hinc, hdet, ht, hp, he⟩ :=
    exists_transverse_detecting_carrier_of_nonexceptional hn hk hs hker hnode
  exact ⟨ξ, hcoord, hchar, hnormal, hinc, hdet, ht, hp, he⟩

/-- A selected carrier lies outside the complete bad-subspace union
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem CarrierSeed.not_mem_badSubspaceUnion {n : ℕ} (hn : 5 ≤ n)
    {k s ξ : Euclidean n} (h : CarrierSeed k s ξ) : ξ ∉ cubeBadSubspaceUnion n := by
  have hreg := regular_of_quadratic_reciprocal_ne_zero
    h.coordinates_ne_zero h.characteristic h.normal_ne_zero
  have hξ : ξ ≠ 0 := by
    intro hz
    exact h.coordinates_ne_zero ⟨0, by omega⟩ (by simp [hz])
  intro hbad
  exact hreg ((cubeDeterminant_multiple_iff_strata hn hξ).mpr
    ((mem_cubeBadSubspaceUnion_iff ξ).mp hbad)).2

end JanetCartan.FrozenMenu
