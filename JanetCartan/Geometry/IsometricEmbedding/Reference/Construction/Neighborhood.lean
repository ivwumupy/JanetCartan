module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Construction.Cube
public import JanetCartan.Geometry.IsometricEmbedding.Normal.SmoothProjection

/-! Persistence of the actual normal rank in Proposition `app:ch_seed:prop:seed-analytic`.
The tangent and normal maps together are surjective at the center. A fixed right inverse
reduces persistence to openness of injectivity for finite-dimensional endomorphisms.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius Topology

namespace JanetCartan.ReferenceConstruction

/-- Proposition `app:ch_seed:prop:seed-analytic`: combine tangent and normal directions
in one map into the fixed ambient space. -/
def tangentNormalMap {n N : ℕ} (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    (Euclidean n × MetricTensor n) →L[ℝ] Euclidean N :=
  LinearMap.toContinuousLinearMap
    ({
      toFun := fun z ↦ fderiv ℝ F x z.1 + normalMap F x z.2
      map_add' := by
        intro z w
        simp only [Prod.fst_add, Prod.snd_add, normalMap, map_add, Matrix.add_apply,
          add_smul, Finset.sum_add_distrib]
        abel
      map_smul' := by
        intro c z
        change fderiv ℝ F x (c • z.1) + normalMap F x (c • z.2) =
          c • (fderiv ℝ F x z.1 + normalMap F x z.2)
        simp only [normalMap, map_smul, Matrix.smul_apply, smul_eq_mul, mul_smul,
          Finset.smul_sum, smul_add] } : (Euclidean n × MetricTensor n) →ₗ[ℝ] Euclidean N)

/-- Proposition `app:ch_seed:prop:seed-analytic`: surjectivity of the combined map is
exactly full normal rank, with no choice of moving normal frame. -/
theorem tangentNormalMap_surjective_iff {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) :
    Function.Surjective (tangentNormalMap F x) ↔
      Set.range (normalMap F x) = (normalSpace F x : Set _) := by
  constructor
  · intro h
    ext w
    constructor
    · rintro ⟨H, rfl⟩
      exact normalMap_mem_normalSpace F x H
    · intro hw
      obtain ⟨⟨v, H⟩, hH⟩ := h w
      refine ⟨H, ?_⟩
      have hp := congrArg (normalProjection F x) hH
      change normalProjection F x (fderiv ℝ F x v + normalMap F x H) = _ at hp
      simpa only [map_add, normalProjection_fderiv, normalProjection_normalMap,
        zero_add, normalProjection_eq_self_of_mem_normalSpace hw] using hp
  · intro h w
    have ht : tangentProjection F x w ∈ (fderiv ℝ F x).range :=
      Subtype.coe_prop _
    obtain ⟨v, hv⟩ := ht
    have hn := normalProjection_mem_normalSpace F x w
    change normalProjection F x w ∈ (normalSpace F x : Set _) at hn
    rw [← h] at hn
    obtain ⟨H, hH⟩ := hn
    refine ⟨(v, H), ?_⟩
    change fderiv ℝ F x v + normalMap F x H = w
    rw [show fderiv ℝ F x v = tangentProjection F x w from hv, hH,
      tangentProjection_add_normalProjection]

/-- Proposition `app:ch_seed:prop:seed-analytic`: the combined tangent and normal map
is continuous for a smooth global immersion. -/
theorem continuous_tangentNormalMap {n N : ℕ} {F : Euclidean n → Euclidean N}
    (hF : ContDiff ℝ ∞ F) (himm : IsImmersionOn F Set.univ) :
    Continuous (tangentNormalMap F) := by
  apply continuous_clm_apply.mpr
  intro z
  change Continuous (fun x ↦ fderiv ℝ F x z.1 + normalMap F x z.2)
  apply Continuous.add ((hF.fderiv_right (m := ∞) (by simp)).continuous.clm_apply
    continuous_const)
  unfold normalMap
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (continuous_const (y := z.2 i j)).smul (contDiffOn_univ.mp
    (contDiffOn_secondFundamentalForm (r := 0) isOpen_univ hF.contDiffOn
      (by simp) himm i j)).continuous

/-- Proposition `app:ch_seed:prop:seed-analytic`: full normal rank persists on a ball
around any full-rank point of a smooth global immersion. -/
theorem exists_ball_fullNormalRank {n N : ℕ} {F : Euclidean n → Euclidean N}
    (hF : ContDiff ℝ ∞ F) (himm : IsImmersionOn F Set.univ) {x : Euclidean n}
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set _)) :
    ∃ r : ℝ, 0 < r ∧ HasFullNormalRankOn F (Metric.ball x r) := by
  let A := tangentNormalMap F
  have hA : Function.Surjective (A x) := (tangentNormalMap_surjective_iff F x).mpr hrank
  obtain ⟨R, hR⟩ := (A x).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hA)
  let R' := R.toContinuousLinearMap
  have hid : (A x).comp R' = ContinuousLinearMap.id ℝ _ := by
    apply ContinuousLinearMap.ext
    intro z
    exact LinearMap.congr_fun hR z
  have hc : Continuous (fun y ↦ (A y).comp R') :=
    (continuous_tangentNormalMap hF himm).clm_comp continuous_const
  have hi : ∀ᶠ y in 𝓝 x, Function.Injective ((A y).comp R') :=
    hc.continuousAt.eventually (ContinuousLinearMap.isOpen_injective.mem_nhds
      (by
        change Function.Injective ((A x).comp R')
        rw [hid]
        exact Function.injective_id))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hi
  refine ⟨r, hr, ?_⟩
  intro y hy
  apply (tangentNormalMap_surjective_iff F y).mp
  have hs := LinearMap.injective_iff_surjective.mp (hball hy)
  intro w
  obtain ⟨z, hz⟩ := hs w
  exact ⟨R' z, hz⟩

/-- Proposition `app:ch_seed:prop:seed-analytic`: the explicit cube bending has full
normal rank on an actual open ball about the center. -/
theorem cubeBending_fullNormalRank_ball {n : ℕ} (hn : 5 ≤ n) :
    ∃ r : ℝ, 0 < r ∧ HasFullNormalRankOn (cubeBending n) (Metric.ball 0 r) := by
  have himm : IsImmersionOn (cubeBending n) Set.univ :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one)
      (fun x _ ↦ cubeBending_inducedMetric (by omega) x)
  exact exists_ball_fullNormalRank (cubeBending_analyticOnNhd n).contDiff himm
    (cubeBending_fullNormalRank_zero hn)

end JanetCartan.ReferenceConstruction
