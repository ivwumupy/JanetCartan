module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# A compact admissible neighborhood of the reference jet

For `app:ch_seed:setup:seed-current` and `app:ch_seed:rem:seed-map-topology`.
These are prerequisites of the current geometric neighborhood: neither of the
jet invertibility conditions nor compact range containment is assumed.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius Topology
open JanetCartan.ProjectedStressFrame JanetCartan.AmbientResponse

namespace JanetCartan.CurrentGeometricNeighborhood
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

/-- The reference metric identity gives immersion everywhere, as used in
`app:ch_seed:setup:seed-current`. -/
theorem reference_isImmersion {n : ℕ} (G : FlatReference n) (x : Euclidean n) :
    Function.Injective (fderiv ℝ G.map x) := by
  exact isImmersionOn_of_isIsometricOn (s := Set.univ) (g := fun _ ↦ 1)
    (fun _ _ ↦ Matrix.PosDef.one) (fun {y} _ ↦ G.inducedMetric_eq_one y) x (Set.mem_univ x)

/-- The common admissible locus retains both inverses in the literal stress
formula of `app:ch_seed:setup:seed-current`. -/
theorem isOpen_stressJet_units {n N : ℕ} :
    IsOpen {J : StressJet n N | IsUnit (jetMetric J) ∧ IsUnit (jetAmbient J)} := by
  have hg : IsOpen {J : StressJet n N | IsUnit (jetMetric J)} :=
    Units.isOpen.preimage (contDiff_jetMetric (n := n) (N := N)).continuous
  have hA : ContinuousOn (@jetAmbient n N) {J | IsUnit (jetMetric J)} :=
    fun J hJ ↦ (contDiffAt_jetAmbient hJ).continuousAt.continuousWithinAt
  exact hA.isOpen_inter_preimage hg Units.isOpen

private theorem compact_jet_neighborhood {n N : ℕ} {S : Set (StressJet n N)}
    (hS : IsCompact S)
    (hsub : S ⊆ {J | IsUnit (jetMetric J) ∧ IsUnit (jetAmbient J)}) :
    ∃ d > 0, ∃ L : Set (StressJet n N), IsCompact L ∧
      (∀ J ∈ L, IsUnit (jetMetric J) ∧ IsUnit (jetAmbient J)) ∧
      (∀ J₀ ∈ S, ∀ J : StressJet n N, ‖J - J₀‖ ≤ d → J ∈ L) := by
  let : ProperSpace (StressJet n N) := FiniteDimensional.proper ℝ (StressJet n N)
  let : LocallyCompactSpace (StressJet n N) := locallyCompact_of_proper (α := StressJet n N)
  obtain ⟨L, hL, hSL, hLU⟩ := exists_compact_between hS
    (isOpen_stressJet_units (n := n) (N := N)) hsub
  obtain ⟨d, hd, hball⟩ := lebesgue_number_lemma_of_metric hS
    (c := fun _ : Unit ↦ interior L) (fun _ ↦ isOpen_interior)
    (by simpa only [Set.iUnion_const] using hSL)
  refine ⟨d / 2, half_pos hd, L, hL, fun J hJ ↦ hLU hJ, ?_⟩
  intro J₀ hJ₀ J hJ
  obtain ⟨_, hb⟩ := hball J₀ hJ₀
  apply interior_subset (hb ?_)
  change dist J J₀ < d
  rw [dist_eq_norm J J₀]
  exact hJ.trans_lt (half_lt_self hd)

/-- Compactness and the actual reference rank yield a positive-radius compact
jet neighborhood in both unit loci (`app:ch_seed:rem:seed-map-topology`).
Its radius and set depend only on the fixed reference and the outer radius. -/
theorem exists_reference_jet_neighborhood {n : ℕ} (G : FlatReference n)
    {R : ℝ} (hR : R < G.domain.chartRadius) :
    ∃ d > 0, ∃ L : Set (StressJet n (embeddingDimension n)), IsCompact L ∧
      (∀ J ∈ L, IsUnit (jetMetric J) ∧ IsUnit (jetAmbient J)) ∧
      (∀ x ∈ Metric.closedBall (0 : Euclidean n) R, ∀ J : StressJet n (embeddingDimension n),
        ‖J - stressJet G.map x‖ ≤ d → J ∈ L) := by
  let S := stressJet G.map '' Metric.closedBall (0 : Euclidean n) R
  have hS : IsCompact S := (isCompact_closedBall (0 : Euclidean n) R).image
    (contDiff_stressJet G.contDiff).continuous
  have hsub : S ⊆ {J | IsUnit (jetMetric J) ∧ IsUnit (jetAmbient J)} := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨isUnit_jetMetric_stressJet (reference_isImmersion G x), ?_⟩
    rw [jetAmbient_stressJet (G.contDiff.contDiffAt.of_le (by simp))
      (reference_isImmersion G x)]
    exact ambientNormalOperator_isUnit (G.fullNormalRank x
      ((Metric.closedBall_subset_ball hR) hx))
  obtain ⟨d, hd, L, hL, hu, hnear⟩ := compact_jet_neighborhood hS hsub
  exact ⟨d, hd, L, hL, hu, fun x hx J hJ ↦ hnear _ ⟨x, hx, rfl⟩ J hJ⟩

end JanetCartan.CurrentGeometricNeighborhood
