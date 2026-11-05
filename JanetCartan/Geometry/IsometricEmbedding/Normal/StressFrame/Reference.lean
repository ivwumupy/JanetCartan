module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.StressFrame.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Construction.Cube

/-!
# The smooth stress frame near the actual cube reference

All reference rank and kernel hypotheses are discharged using the explicit
analytic circular bending of `app:ch_seed:prop:seed-analytic`. The resulting
frame is the one in `app:ch_background:defn:bg-geometry`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius ContDiff Topology

namespace JanetCartan.StressFrame

open ReferenceConstruction

/-- `app:ch_seed:prop:seed-analytic`: the actual reference second form is
surjective already on symmetric tensors. -/
theorem symmetricNormalMap_cubeBending_surjective {n : ℕ} (hn : 5 ≤ n) :
    Function.Surjective (symmetricNormalMap (cubeBending n) 0) := by
  intro w
  let c : EuclideanSpace ℝ (CoordinatePair n) := WithLp.toLp 2 fun p ↦
    inner ℝ (centerNormal n (Fintype.card (CoordinatePair n))
      (Fintype.equivFin (CoordinatePair n) p)) w.val
  obtain ⟨H, hs, hH⟩ := cubeNormalMap_surjective hn c
  refine ⟨⟨H, hs⟩, Subtype.ext ?_⟩
  apply cubeBending_normal_ext (by omega) (cubeBending_normalMap_mem_normalSpace n H) w.property
  intro p
  rw [cubeBending_normalMap_row (by omega), hH]

/-- `app:ch_seed:prop:seed-analytic`: the actual reference stress kernel
is precisely the frozen symmetric cube-stress span. -/
theorem symmetricNormalMap_cubeBending_ker {n : ℕ} (hn : 5 ≤ n) :
    (symmetricNormalMap (cubeBending n) 0).ker =
      Submodule.span ℝ (Set.range (cubeSymmetricStress n)) := by
  rw [← cubeNormalLinearMapOnSymmetric_ker hn]
  ext H
  change symmetricNormalMap (cubeBending n) 0 H = 0 ↔ cubeNormalMap n H.val = 0
  rw [← cubeBending_normalMap_eq_zero_iff (by omega)]
  exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩

/-- `app:ch_background:defn:bg-carriers`: the actual reference projections
recover exactly the frozen stresses at the center. -/
theorem geometricCubeStress_cubeBending_zero {n : ℕ} (hn : 5 ≤ n) (i : Fin n) :
    geometricCubeStress (cubeBending n) 0 i = cubeSymmetricStress n i := by
  apply Submodule.starProjection_eq_self_iff.mpr
  rw [symmetricNormalMap_cubeBending_ker hn]
  exact Submodule.subset_span (Set.mem_range_self i)

/-- `app:ch_background:defn:bg-geometry`: the actual analytic cube reference
has a ball with a smooth projected stress basis and a uniform positive Gram
gap. No rank, independence, dimension or gap hypothesis is left to discharge. -/
theorem exists_cubeBending_ball_smooth_stressFrame {n : ℕ} (hn : 5 ≤ n) :
    ∃ ε > 0, ∃ γ > 0,
      (∀ i, ContDiffOn ℝ ∞ (fun y ↦ geometricCubeStress (cubeBending n) y i)
        (Metric.ball 0 ε)) ∧
      ∀ y ∈ Metric.ball 0 ε, Function.Surjective (symmetricNormalMap (cubeBending n) y) ∧
        HasCubeStressFrame (symmetricNormalMap (cubeBending n) y).ker γ := by
  have himm : IsImmersionOn (cubeBending n) Set.univ :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one)
      (fun x _ ↦ cubeBending_inducedMetric (by omega) x)
  obtain ⟨ε, hε, γ, hγ, _, hsmooth, hframe⟩ := exists_ball_smooth_geometricCubeStress hn
    isOpen_univ (cubeBending_analyticOnNhd n).contDiff.contDiffOn himm (Set.mem_univ 0)
    (symmetricNormalMap_cubeBending_surjective hn) (symmetricNormalMap_cubeBending_ker hn)
  exact ⟨ε, hε, γ, hγ, hsmooth, hframe⟩

/-- `app:ch_waves:thm:leading` and `app:ch_background:defn:bg-geometry`:
a single neighborhood of the actual cube reference gives smooth projected
bases and a uniform positive Gram gap for every smooth immersion in that
neighborhood. The two strict inequalities describe its normal-projection
and second-form operator neighborhood, allowing the normal spaces to vary. -/
theorem exists_cubeBending_smooth_stressFrame_neighborhood {n : ℕ} (hn : 5 ≤ n) :
    ∃ δ > 0, ∃ γ > 0,
      ∀ (G : Euclidean n → Euclidean (n + Fintype.card (CoordinatePair n)))
        (s : Set (Euclidean n)), IsOpen s → ContDiffOn ℝ ∞ G s → IsImmersionOn G s →
        (∀ y ∈ s, ‖normalProjection (cubeBending n) 0 - normalProjection G y‖ < 1 ∧
          ‖fixedSymmetricNormalMap (cubeBending n) 0 G y -
            symmetricNormalMap (cubeBending n) 0‖ < δ) →
        (∀ i, ContDiffOn ℝ ∞ (fun y ↦ geometricCubeStress G y i) s) ∧
        ∀ y ∈ s, Function.Surjective (symmetricNormalMap G y) ∧
          HasCubeStressFrame (symmetricNormalMap G y).ker γ := by
  obtain ⟨δ, hδ, γ, hγ, h⟩ := exists_operator_cubeStressFrame_neighborhood hn
    (symmetricNormalMap (cubeBending n) 0) (symmetricNormalMap_cubeBending_surjective hn)
    (symmetricNormalMap_cubeBending_ker hn)
  refine ⟨δ, hδ, γ, hγ, fun G s hs hG himm hclose ↦ ?_⟩
  have hp := fun y hy ↦ (hclose y hy).1
  have hb := fun y hy ↦ (h (fixedSymmetricNormalMap (cubeBending n) 0 G y) (hclose y hy).2).1
  refine ⟨fun i ↦ contDiffOn_geometricCubeStress_of_comparison (cubeBending n) 0
    hs hG (by simp) himm hp hb i, fun y hy ↦ ?_⟩
  constructor
  · intro w
    obtain ⟨H, hH⟩ := hb y hy (NormalRankStability.projectionBetween
      (normalSpace G y) (normalSpace (cubeBending n) 0) w)
    exact ⟨H, NormalRankStability.projectionBetween_injective _ _ (hp y hy) hH⟩
  · have hf := (h _ (hclose y hy).2).2
    rwa [fixedSymmetricNormalMap_ker (cubeBending n) G 0 y (hp y hy)] at hf

end JanetCartan.StressFrame
