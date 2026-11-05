module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.RetainedCorrection

/-!
# Buffered localization inside the original retained cover

The sharp slice theorem needs a carrier neighborhood strictly inside a graded
working ball. Refine the original open carrier cover before any low budgets,
keeping a parent-cell map. Thus every refined label uses its parent's selected
minor, flows and original scalar norm domain. No original covering ball is
shrunk without a new coverage proof.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.RawPrimary
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation

/-- A finite refinement of the original retained open carrier cover with the
precise `ρ/4` label margin used by `exists_uniform_canonical_rawSliceSobolev`.
The doubled local working ball is contained in its original parent ball.
These choices depend only on the original phase reference and cover, so they
precede immersion/scalar budgets (`app:ch_waves:thm:individual`). -/
theorem exists_retained_raw_chart_refinement
    {n : ℕ} {P : Patch n} {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (centers : Finset (parameterCube P.radius)) (σ : centers → ℝ)
    (hcover : ∀ z ∈ parameterCube P.radius, ∃ j : centers,
      ((0 : Euclidean n), (z, T.reference.spatialPatch z)) ∈
        ball ((0 : Euclidean n), (j.1.1, T.reference.spatialPatch j.1.1)) (σ j)) :
    ∃ labels : Finset (parameterCube P.radius), ∃ parent : labels → centers,
    ∃ ρ : labels → ℝ, (∀ i, 0 < ρ i) ∧
      (∀ i, closedBall ((0 : Euclidean n), (i.1.1, T.reference.spatialPatch i.1.1))
          (2 * ρ i) ⊆
        ball ((0 : Euclidean n), ((parent i).1.1,
          T.reference.spatialPatch (parent i).1.1)) (σ (parent i))) ∧
      ∀ z ∈ parameterCube P.radius, ∃ i : labels,
        (z, T.reference.spatialPatch z) ∈
          ball (i.1.1, T.reference.spatialPatch i.1.1) (ρ i / 4) := by
  classical
  let graph := fun z : Euclidean 3 ↦ (z, T.reference.spatialPatch z)
  choose parent hp using fun z : parameterCube P.radius ↦ hcover z.1 z.2
  let ρ := fun z : parameterCube P.radius ↦
    (σ (parent z) - dist (graph z.1) (graph (parent z).1.1)) / 4
  have hd (z : parameterCube P.radius) :
      dist (graph z.1) (graph (parent z).1.1) < σ (parent z) := by
    have hh := mem_ball.mp (hp z)
    change dist ((0 : Euclidean n), graph z.1) (0, graph (parent z).1.1) < _ at hh
    rwa [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] at hh
  have hρ (z : parameterCube P.radius) : 0 < ρ z := by
    dsimp only [ρ]
    linarith [hd z]
  have hsub (z : parameterCube P.radius) :
      closedBall ((0 : Euclidean n), graph z.1) (2 * ρ z) ⊆
        ball ((0 : Euclidean n), graph (parent z).1.1) (σ (parent z)) := by
    apply closedBall_subset_ball'
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    dsimp only [ρ]
    linarith [hd z]
  have hgraph : ContinuousOn graph (parameterCube P.radius) :=
    continuousOn_id.prodMk ((T.reference.spatialPatch_smooth hP).continuousOn.mono
      (parameterCube_subset_doubledInterior hP.1))
  let O := fun z : parameterCube P.radius ↦
    (fun w : parameterCube P.radius ↦ graph w.1) ⁻¹' ball (graph z.1) (ρ z / 4)
  have hO (z) : IsOpen (O z) := isOpen_ball.preimage hgraph.domRestrict
  have hcov : (univ : Set (parameterCube P.radius)) ⊆ ⋃ z, O z := by
    intro z _
    exact mem_iUnion.mpr ⟨z, mem_ball_self (div_pos (hρ z) (by norm_num))⟩
  let : CompactSpace (parameterCube P.radius) :=
    isCompact_iff_compactSpace.mp (isCompact_parameterCube P.radius)
  obtain ⟨labels, hlabels⟩ := isCompact_univ.elim_finite_subcover O hO hcov
  refine ⟨labels, fun i ↦ parent i.1, fun i ↦ ρ i.1,
    fun i ↦ hρ i.1, fun i ↦ hsub i.1, ?_⟩
  intro z hz
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hlabels (mem_univ (⟨z, hz⟩ : parameterCube P.radius)))
  exact ⟨⟨i, hi⟩, hzi⟩

end JanetCartan.RawPrimary
