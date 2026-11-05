module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Strata
public import JanetCartan.Geometry.IsometricEmbedding.Reference.SignedPairs.Bounds
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # A common closed angular set

The compact set in Step 2 of `app:ch_seed:prop:seed-actual-menu` is cut out
by quantitative projection inequalities. Its closedness includes all limiting
normalized chords without any lower bound on the parameter spacing.
-/

@[expose] public noncomputable section

namespace JanetCartan.SignedPairs

/-- Projection away from a frozen bad subspace in
`app:ch_seed:eq:seed-actual-chord`, with ambient Euclidean codomain. -/
def projectAway {n : ℕ} (L : Submodule ℝ (Euclidean n)) :
    Euclidean n →L[ℝ] Euclidean n := Lᗮ.starProjection

/-- The projection used in `app:ch_seed:eq:seed-actual-chord` is contractive. -/
theorem norm_projectAway_le {n : ℕ} (L : Submodule ℝ (Euclidean n)) (v : Euclidean n) :
    ‖projectAway L v‖ ≤ ‖v‖ := Lᗮ.norm_starProjection_apply_le v

/-- The projection vanishes on its forbidden subspace
(`app:ch_seed:prop:seed-strata`). -/
theorem projectAway_eq_zero {n : ℕ} (L : Submodule ℝ (Euclidean n))
    {v : Euclidean n} (hv : v ∈ L) : projectAway L v = 0 :=
  L.starProjection_orthogonal_apply_eq_zero hv

/-- The common compact angular set of `app:ch_seed:prop:seed-actual-menu`,
Step 2, specified using the frozen bad-subspace family. -/
def angularSet (n : ℕ) (γ : ℝ) : Set (Euclidean n) :=
  {v | ‖v‖ = 1 ∧ ∀ L ∈ cubeBadSubspaces n, γ ≤ ‖projectAway L v‖}

/-- The angular inequalities survive limits of normalized short chords
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem isClosed_angularSet (n : ℕ) (γ : ℝ) : IsClosed (angularSet n γ) := by
  simp only [angularSet, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_eq continuous_norm continuous_const).inter
    (isClosed_iInter fun L ↦ isClosed_iInter fun _ ↦
      isClosed_le continuous_const (projectAway L).continuous.norm)

/-- Finite-dimensional unit directions with the closed projection gaps form
a compact set (`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem isCompact_angularSet (n : ℕ) (γ : ℝ) : IsCompact (angularSet n γ) := by
  apply (isCompact_sphere (0 : Euclidean n) 1).of_isClosed_subset (isClosed_angularSet n γ)
  intro v hv
  simpa only [Metric.mem_sphere, dist_zero_right] using hv.1

/-- Both global signs belong to the same angular set
(`app:rem:exhaustive-signed-pairs`). -/
theorem neg_mem_angularSet {n : ℕ} {γ : ℝ} {v : Euclidean n}
    (hv : v ∈ angularSet n γ) : -v ∈ angularSet n γ := by
  constructor
  · simpa using hv.1
  · intro L hL
    simpa using hv.2 L hL

/-- The projection gap is a literal distance gap from the whole frozen
nonprincipal cone, not only from sampled directions
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem angularSet_distance_gap {n : ℕ} {γ : ℝ} {v w : Euclidean n}
    (hv : v ∈ angularSet n γ) (hw : w ∈ cubeBadSubspaceUnion n) :
    γ ≤ dist v w := by
  obtain ⟨L, hL, hw⟩ := Set.mem_iUnion₂.mp hw
  calc
    γ ≤ ‖projectAway L v‖ := hv.2 L hL
    _ = ‖projectAway L (v - w)‖ := by rw [map_sub, projectAway_eq_zero L hw, sub_zero]
    _ ≤ ‖v - w‖ := norm_projectAway_le L _
    _ = dist v w := (dist_eq_norm v w).symm

/-- The common angular set avoids the frozen nonprincipal set
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem angularSet_disjoint_bad {n : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    Disjoint (angularSet n γ) (cubeBadSubspaceUnion n) := by
  rw [Set.disjoint_left]
  intro v hv hw
  have h := angularSet_distance_gap hv hw
  simp only [dist_self] at h
  exact (not_le_of_gt hγ) h

/-- Every limit of protected directions stays in the same compact symmetric
set (`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem closure_subset_angularSet {n : ℕ} {γ : ℝ} {D : Set (Euclidean n)}
    (hD : D ⊆ angularSet n γ) : closure D ⊆ angularSet n γ :=
  closure_minimal hD (isClosed_angularSet n γ)

/-- With the manuscript's dimension hypothesis, every direction in the compact
angular set has rank at least `n-1`, and every characteristic there is simple
(`app:ch_seed:prop:seed-strata`, `app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem angularSet_regular {n : ℕ} (hn : 5 ≤ n) {γ : ℝ} (hγ : 0 < γ)
    {v : Euclidean n} (hv : v ∈ angularSet n γ) :
    n - 1 ≤ (cubePencil v).rank ∧
      (cubeDeterminant v = 0 → fderiv ℝ cubeDeterminant v ≠ 0) := by
  have hbad : v ∉ cubeBadSubspaceUnion n :=
    (Set.disjoint_left.mp (angularSet_disjoint_bad hγ)) hv
  exact ⟨cubePencil_rank_ge_of_not_mem_badSubspaceUnion hn hbad,
    fderiv_cubeDeterminant_ne_zero_of_not_mem_badSubspaceUnion hn hbad⟩

end JanetCartan.SignedPairs
