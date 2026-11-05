module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.RetainedAssembly.ExternalWeights.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FixedCutoffs

/-!
# One physical buffer for the original external weights

Choose the measurement radius from the full closed supports of the already
selected external cutoffs. It precedes the source scale, every history and all
operator bounds. In particular this construction does not take the infimum of
radii that were chosen separately for each positive source scale.

The original retained-cell inclusions then supply `hflow₀` and `hflowσ` in
`RetainedAssembly.NormalizedMeanSource.exists_current_referenceSource_sobolev_bounds`
on these same supports. The carrier measure and all external weights are
unchanged. Uniform normal/inverse estimates on the resulting fixed physical
cutoffs remain separate analytic obligations.
-/

@[expose] public noncomputable section
open Set Metric
namespace JanetCartan.PositiveBackground
open ContinuumRow RetainedAssembly.ExternalWeights

/-- A finite family of the supplied external weights admits one common
physical measurement/source buffer inside the original retained cells. The
entire weight support is retained, including the collar outside the detector
projection. `cap` imposes the original mask-radius margin before any source
scale is chosen (`app:ch_background:prop:bg-positive`,
`app:ch_background:prop:bg-normalized`, `new:sec:order-of-choices`).

Producer of `hsupport`: the original selection by
`RetainedAssembly.ExternalWeights.exists_externalWeights`. The returned
product inclusions are consumed with the SAME retained-cell flow maps by
`RetainedAssembly.NormalizedMeanSource`; no operator estimate is assumed. -/
theorem exists_fixed_weight_measurement_buffer {n : ℕ} {ι : Type*} [Fintype ι]
    (E : ι → Set (Euclidean n × CarrierParameter)) (hE : ∀ i, IsOpen (E i))
    (χ : ι → CarrierParameter → ℝ) (hcompact : ∀ i, HasCompactSupport (χ i))
    (hsupport : ∀ i, tsupport (χ i) ⊆ carrierNeighborhood (E i))
    {U : Set (Euclidean n)} (hU : IsOpen U) (h0U : (0 : Euclidean n) ∈ U)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ (r : ℝ) (hr : 0 < r), 4 * r < 1 / 2 ∧ 6 * r < cap ∧ 6 * r < 1 / 2 ∧
      closedBall (0 : Euclidean n) (6 * r) ⊆ U ∧
      ∃ V : ι → Set CarrierParameter,
        (∀ i, IsOpen (V i)) ∧ (∀ i, tsupport (χ i) ⊆ V i) ∧
        (∀ i, closedBall (0 : Euclidean n) (6 * r) ×ˢ V i ⊆ E i) ∧
        ∀ (i : ι) (j : Fin 3),
          tsupport (FixedCutoffs.physical (n := n) hr j) ×ˢ tsupport (χ i) ⊆ E i := by
  classical
  have hprod (i : ι) : ({(0 : Euclidean n)} : Set (Euclidean n)) ×ˢ tsupport (χ i) ⊆ E i := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hx' : x = 0 := hx
    subst x
    exact hsupport i hz
  choose W V hW hV h0W hKV hWV using fun i ↦
    generalized_tube_lemma isCompact_singleton (hcompact i) (hE i) (hprod i)
  have hopen : IsOpen (U ∩ ⋂ i, W i) := hU.inter (isOpen_iInter_of_finite hW)
  have hzero : (0 : Euclidean n) ∈ U ∩ ⋂ i, W i :=
    ⟨h0U, mem_iInter.mpr fun i ↦ h0W i (mem_singleton 0)⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  let r := min (ε / 12) (min (cap / 12) (1 / 24))
  have hr : 0 < r := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hre : r ≤ ε / 12 := min_le_left _ _
  have hrc : r ≤ cap / 12 := (min_le_right _ _).trans (min_le_left _ _)
  have hrone : r ≤ 1 / 24 := (min_le_right _ _).trans (min_le_right _ _)
  have hclosed : closedBall (0 : Euclidean n) (6 * r) ⊆ U ∩ ⋂ i, W i :=
    (closedBall_subset_ball (by linarith : 6 * r < ε)).trans hball
  have hcell (i : ι) : closedBall (0 : Euclidean n) (6 * r) ×ˢ V i ⊆ E i := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    exact hWV i ⟨mem_iInter.mp (hclosed hx).2 i, hz⟩
  refine ⟨r, hr, by linarith, by linarith, by linarith,
    hclosed.trans inter_subset_left, V, hV, hKV, hcell, ?_⟩
  intro i j
  apply Subset.trans _ (hcell i)
  exact prod_mono ((FixedCutoffs.physical_tsupport_four hr j).trans
    (closedBall_subset_closedBall (by linarith))) (hKV i)

end JanetCartan.PositiveBackground
