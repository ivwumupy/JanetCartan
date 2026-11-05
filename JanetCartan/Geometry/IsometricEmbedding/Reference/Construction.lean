module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Construction.Embedding

/-!
# Construction of the flat reference

The finite composition of circular bendings from Proposition
`app:ch_seed:prop:seed-analytic` is globally analytic, fixes the center, and has
exactly the flat metric. Its actual center second forms are the prescribed cube
rank-one forms. Its actual normal map is surjective on a neighborhood and its
center kernel is precisely the frozen cube stress space.

`exists_analytic_flatReference` assembles these checked facts in the prescribed
Janet–Cartan target dimension. The public `exists_flatReference` theorem applies
this construction.
-/

@[expose] public noncomputable section

namespace JanetCartan

open ReferenceConstruction

/-- Proposition `app:ch_seed:prop:seed-analytic`: the explicit circular-bending
construction supplies an analytic `FlatReference`, including actual full normal
rank throughout its chart, the exact center stress kernel, and a topological
embedding on the chart. -/
theorem exists_analytic_flatReference_embedding {n : ℕ} (hn : 5 ≤ n) :
    ∃ G : FlatReference n, AnalyticOnNhd ℝ G.map Set.univ ∧
      Topology.IsEmbedding (fun x : G.domain.chart n ↦ G.map x) := by
  obtain ⟨r, hr, hrank⟩ := cubeBending_fullNormalRank_ball hn
  obtain ⟨rₑ, hrₑ, hbound⟩ := cubeBending_lower_distance_bound (show 0 < n by omega)
  let D : LocalDomain :=
    { coreRadius := min r (min rₑ (1 / 4)) / 2
      chartRadius := min r (min rₑ (1 / 4))
      coreRadius_pos := half_pos (lt_min hr (lt_min hrₑ (by norm_num)))
      coreRadius_lt_chartRadius := half_lt_self (lt_min hr (lt_min hrₑ (by norm_num)))
      chartRadius_lt_half := lt_of_le_of_lt
        ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num) }
  have hchart : HasFullNormalRankOn (cubeBending n) (D.chart n) := by
    intro x hx
    apply hrank x
    exact lt_of_lt_of_le (show dist x 0 < min r (min rₑ (1 / 4)) from hx) (min_le_left _ _)
  have hembedding : Topology.IsEmbedding (fun x : D.chart n ↦ cubeBending n x) := by
    have ha : AntilipschitzWith 2 (fun x : D.chart n ↦ cubeBending n x) := by
      apply AntilipschitzWith.of_le_mul_dist
      intro x y
      have hsub : D.chart n ⊆ Metric.ball 0 rₑ := by
        intro z hz
        exact lt_of_lt_of_le (show dist z 0 < min r (min rₑ (1 / 4)) from hz)
          ((min_le_right _ _).trans (min_le_left _ _))
      exact hbound x (hsub x.property) y (hsub y.property)
    exact ha.isEmbedding (((cubeBending_analyticOnNhd n).contDiff (n := 0)).continuous.comp
      continuous_subtype_val)
  have hex : ∃ F : Euclidean n → Euclidean (n + Fintype.card (CoordinatePair n)),
      AnalyticOnNhd ℝ F Set.univ ∧ F 0 = 0 ∧ (∀ x, inducedMetric F x = 1) ∧
      HasFullNormalRankOn F (D.chart n) ∧
      stressSpace F 0 = (Submodule.span ℝ (Set.range (cubeStress n)) : Set (MetricTensor n)) ∧
      Topology.IsEmbedding (fun x : D.chart n ↦ F x) :=
    ⟨cubeBending n, cubeBending_analyticOnNhd n, cubeBending_zero n,
      cubeBending_inducedMetric (by omega), hchart, cubeBending_stressSpace_zero hn, hembedding⟩
  rw [cubeBending_ambientDimension n] at hex
  obtain ⟨F, hF, hzero, hmetric, hrank, hkernel, hemb⟩ := hex
  exact ⟨{ domain := D
           map := F
           contDiff := hF.contDiff
           map_zero := hzero
           inducedMetric_eq_one := hmetric
           fullNormalRank := hrank
           stressSpace_zero := hkernel }, hF, hemb⟩

/-- Proposition `app:ch_seed:prop:seed-analytic`: an analytic flat reference exists
with the exact prescribed center stress space. This is the constructive
existence result consumed by `exists_flatReference` in `Reference.lean`. -/
theorem exists_analytic_flatReference {n : ℕ} (hn : 5 ≤ n) :
    ∃ G : FlatReference n, AnalyticOnNhd ℝ G.map Set.univ := by
  obtain ⟨G, hG, _⟩ := exists_analytic_flatReference_embedding hn
  exact ⟨G, hG⟩

end JanetCartan
