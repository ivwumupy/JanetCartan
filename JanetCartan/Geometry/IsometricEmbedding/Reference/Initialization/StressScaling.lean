module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Scaling
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.Smoothness
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Construction
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Dilation.Estimates

import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.SecondJet
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Source scaling of the actual projected stress frame

The stress-frame part of `main:prop:seed`, `main:eq:normalized`, and
`app:ch_seed:setup:seed-current`. The projection is the actual symmetric-kernel
orthogonal projection; no normalized frame is supplied as an extra hypothesis.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius Topology
open Set

namespace JanetCartan.ProjectedStressFrame

variable {n N : ℕ}

/-- The symmetric kernel is the stress space of
`app:ch_seed:setup:seed-current`, expressed as a submodule. -/
theorem mem_symmetricNormalMap_ker_iff {F : Euclidean n → Euclidean N}
    {x : Euclidean n} (H : SymmetricTensor n) :
    H ∈ (symmetricNormalMap F x).ker ↔ H.val ∈ stressSpace F x := by
  change symmetricNormalMap F x H = 0 ↔ H.val.IsSymm ∧ normalMap F x H.val = 0
  exact ⟨fun h ↦ ⟨H.property, congrArg Subtype.val h⟩,
    fun h ↦ Subtype.ext h.2⟩

/-- Source dilation preserves the actual symmetric stress kernel
(`main:eq:normalized`). -/
theorem symmetricNormalMap_ker_sourceDilation {F : Euclidean n → Euclidean N}
    {σ : ℝ} (hσ : 0 < σ) (hF : ContDiff ℝ ∞ F) (x : Euclidean n) :
    (symmetricNormalMap (sourceDilation F σ) x).ker =
      (symmetricNormalMap F (σ • x)).ker := by
  ext H
  rw [mem_symmetricNormalMap_ker_iff, mem_symmetricNormalMap_ker_iff,
    stressSpace_sourceDilation hσ hF]

/-- The exact projected-frame scaling identity for `main:eq:normalized`.
Full normal rank is required only at the corresponding source point; in
particular this applies on the full-rank immersion locus. -/
theorem projectedStress_sourceDilation {F : Euclidean n → Euclidean N}
    {σ : ℝ} (hσ : 0 < σ) (hF : ContDiff ℝ ∞ F) (x : Euclidean n)
    (hrank : Set.range (normalMap F (σ • x)) =
      (normalSpace F (σ • x) : Set (Euclidean N))) (i : Fin n) :
    projectedStress (sourceDilation F σ) x i = projectedStress F (σ • x) i := by
  have hrank' : Set.range (normalMap (sourceDilation F σ) x) =
      (normalSpace (sourceDilation F σ) x : Set (Euclidean N)) := by
    rw [normalMap_sourceDilation_range hσ hF,
      normalSpace_sourceDilation hσ (hF.differentiable (by simp) _)]
    exact hrank
  change stressProjection _ _ (cubeSymmetricStress n i).val = _
  rw [stressProjection_eq_symmetric_starProjection
      ((contDiff_sourceDilation hF).contDiffAt.of_le (by simp)) hrank'
      (cubeSymmetricStress n i),
    symmetricNormalMap_ker_sourceDilation hσ hF]
  exact (stressProjection_eq_symmetric_starProjection
    (hF.contDiffAt.of_le (by simp)) hrank (cubeSymmetricStress n i)).symm

/-- The actual frame at the center of any `FlatReference` is exactly the
frozen cube frame, as required in `app:ch_seed:setup:seed-current`. -/
theorem projectedStress_flatReference_zero (G : FlatReference n) (i : Fin n) :
    projectedStress G.map 0 i = cubeStress n i := by
  have h0 : (0 : Euclidean n) ∈ G.domain.chart n :=
    Metric.mem_ball_self (G.domain.coreRadius_pos.trans G.domain.coreRadius_lt_chartRadius)
  change stressProjection _ _ (cubeSymmetricStress n i).val = _
  rw [stressProjection_eq_symmetric_starProjection
    (G.contDiff.contDiffAt.of_le (by simp)) (G.fullNormalRank 0 h0)
    (cubeSymmetricStress n i)]
  have hmem : cubeSymmetricStress n i ∈ (symmetricNormalMap G.map 0).ker := by
    rw [mem_symmetricNormalMap_ker_iff, G.stressSpace_zero]
    exact Submodule.subset_span (Set.mem_range_self i)
  rw [Submodule.starProjection_eq_self_iff.mpr hmem]
  rfl

/-- A common smooth extension of the finitely many actual reference stresses.
This supplies the global smooth functions used by the dilation estimate in
`main:prop:seed`; agreement is on an open ball, so all ambient jets agree. -/
theorem exists_smooth_projectedStress_extension (G : FlatReference n) :
    ∃ a : ℝ, 0 < a ∧ Metric.ball 0 a ⊆ G.domain.chart n ∧
      ∃ f : Fin n → MetricField n, ∀ i, ContDiff ℝ ∞ (f i) ∧
        EqOn (f i) (fun x ↦ projectedStress G.map x i) (Metric.ball 0 a) := by
  let d := G.domain.chartRadius
  have hd : 0 < d := G.domain.coreRadius_pos.trans G.domain.coreRadius_lt_chartRadius
  let b : ContDiffBump (0 : Euclidean n) := ⟨d / 4, d / 2, by positivity, by linarith⟩
  have hbU : tsupport b ⊆ G.domain.chart n := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  have himm : IsImmersionOn G.map (G.domain.chart n) :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one)
      (fun x _ ↦ G.inducedMetric_eq_one x)
  refine ⟨d / 4, by positivity, Metric.ball_subset_ball (by dsimp [d]; linarith),
    fun i x ↦ b x • projectedStress G.map x i, ?_⟩
  intro i
  have hQ := contDiffOn_projectedStress Metric.isOpen_ball G.contDiff.contDiffOn
    himm G.fullNormalRank i
  constructor
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ G.domain.chart n
    · exact b.contDiff.contDiffAt.smul (hQ.contDiffAt (Metric.isOpen_ball.mem_nhds hx))
    · have hxb : x ∉ tsupport b := fun h ↦ hx (hbU h)
      apply (contDiffAt_const (c := (0 : MetricTensor n))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxb] with y hy
      simp [hy]
  · intro x hx
    change b x • projectedStress G.map x i = projectedStress G.map x i
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx), one_smul]

/-- Uniform source scales and stress estimates on any fixed compact working
box, for `main:prop:seed` and `app:ch_seed:setup:seed-current`.

The open working neighborhood and admissible scale interval are fixed before
any derivative order. Every contraction segment stays in the original rank
chart. In particular `r = 6` gives the required `C * σ` low-norm estimate,
uniformly in the frame index. Only the actual `FlatReference` is an input. -/
theorem exists_projectedStress_dilation_bounds (G : FlatReference n)
    {K : Set (Euclidean n)} (hK : IsCompact K) :
    ∃ U : Set (Euclidean n), IsOpen U ∧ K ⊆ U ∧
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ ≤ 1 ∧
        (∀ σ ∈ Icc (0 : ℝ) σ₀, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ U,
          t • (σ • x) ∈ G.domain.chart n) ∧
        (∀ σ ∈ Ioc (0 : ℝ) σ₀,
          IsImmersionOn (sourceDilation G.map σ) U ∧
          HasFullNormalRankOn (sourceDilation G.map σ) U ∧
          ∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress (sourceDilation G.map σ) x i) U) ∧
        ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ i,
          cNorm K r (fun x ↦ projectedStress (sourceDilation G.map σ) x i -
            cubeStress n i) ≤ C * σ := by
  obtain ⟨a, ha, haU, f, hf⟩ := exists_smooth_projectedStress_extension G
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  let U : Set (Euclidean n) := Metric.ball 0 (R + 1)
  have hU : IsOpen U := Metric.isOpen_ball
  have hKU : K ⊆ U := by
    intro x hx
    simpa [U, Metric.mem_ball, dist_zero_right] using (hKR x hx).trans_lt (by linarith)
  let σ₀ := min 1 (a / (2 * (R + 1)))
  have hσ₀ : 0 < σ₀ := lt_min zero_lt_one (by positivity)
  have hσ₁ : σ₀ ≤ 1 := min_le_left _ _
  have hball (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) σ₀) (x : Euclidean n)
      (hx : x ∈ U) : σ • x ∈ Metric.ball 0 a := by
    have hxnorm : ‖x‖ < R + 1 := by simpa [U, Metric.mem_ball, dist_zero_right] using hx
    have hsmall : σ * (2 * (R + 1)) ≤ a :=
      (le_div_iff₀ (by positivity)).mp (hσ.2.trans (min_le_right _ _))
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ.1]
    have := mul_le_mul_of_nonneg_left hxnorm.le hσ.1
    nlinarith
  have hseg (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) σ₀) (t : ℝ)
      (ht : t ∈ Icc (0 : ℝ) 1) (x : Euclidean n) (hx : x ∈ U) :
      t • (σ • x) ∈ G.domain.chart n := by
    apply haU
    have hnorm : ‖σ • x‖ < a := by simpa [Metric.mem_ball, dist_zero_right] using hball σ hσ x hx
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt hnorm
  have hdom (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) σ₀) :
      MapsTo (fun x ↦ σ • x) U (G.domain.chart n) :=
    fun x hx ↦ haU (hball σ ⟨hσ.1.le, hσ.2⟩ x hx)
  have himm : IsImmersionOn G.map Set.univ :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one)
      (fun x _ ↦ G.inducedMetric_eq_one x)
  refine ⟨U, hU, hKU, σ₀, hσ₀, hσ₁, hseg, ?_, ?_⟩
  · intro σ hσ
    have hi : IsImmersionOn (sourceDilation G.map σ) U :=
      (isImmersionOn_sourceDilation_iff hσ.1 G.contDiff U).mpr
        (fun x _ ↦ himm x (mem_univ x))
    have hr : HasFullNormalRankOn (sourceDilation G.map σ) U :=
      (hasFullNormalRankOn_sourceDilation_iff hσ.1 G.contDiff U).mpr
        (fun x hx ↦ G.fullNormalRank x (by
          obtain ⟨y, hy, rfl⟩ := hx
          exact hdom σ hσ hy))
    exact ⟨hi, hr, fun i ↦ contDiffOn_projectedStress hU
      (contDiff_sourceDilation G.contDiff).contDiffOn hi hr i⟩
  · intro r
    have hb (i : Fin n) := exists_cNorm_dilation_sub_const_bound hK (hf i).1 r
    choose C hC hbound using hb
    have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ ↦ (hC i).le)
    refine ⟨1 + ∑ i, C i, by linarith, ?_⟩
    intro σ hσ i
    have hf0 : f i 0 = cubeStress n i :=
      ((hf i).2 (Metric.mem_ball_self ha)).trans (projectedStress_flatReference_zero G i)
    have heq : cNorm K r (fun x ↦ projectedStress (sourceDilation G.map σ) x i -
        cubeStress n i) = cNorm K r (fun x ↦ f i (σ • x) - f i 0) := by
      apply GeometricProfile.cNorm_eq_of_eventuallyEq
      intro x hx
      filter_upwards [hU.mem_nhds (hKU hx)] with y hy
      rw [projectedStress_sourceDilation hσ.1 G.contDiff y
        (G.fullNormalRank _ (hdom σ hσ hy)), (hf i).2 (hball σ ⟨hσ.1.le, hσ.2⟩ y hy), hf0]
    rw [heq]
    apply (hbound i σ ⟨hσ.1.le, hσ.2.trans hσ₁⟩).trans
    apply mul_le_mul_of_nonneg_right _ hσ.1.le
    have := Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ i)
    linarith

/-- Fix the positive reference scale using only the prescribed low `C⁶`
neighborhood of `app:ch_seed:setup:seed-current`. All higher-order bounds
are obtained afterwards, without changing that scale or the working domain.
Later target accuracies do not occur among the inputs. -/
theorem exists_source_scale_projectedStress_lt (G : FlatReference n)
    {K : Set (Euclidean n)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧
      ∃ U : Set (Euclidean n), IsOpen U ∧ K ⊆ U ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ U, t • (σ • x) ∈ G.domain.chart n) ∧
        IsImmersionOn (sourceDilation G.map σ) U ∧
        HasFullNormalRankOn (sourceDilation G.map σ) U ∧
        (∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress (sourceDilation G.map σ) x i) U) ∧
        (∀ i, cNorm K 6 (fun x ↦ projectedStress (sourceDilation G.map σ) x i -
          cubeStress n i) < ε) ∧
        ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i,
          cNorm K r (fun x ↦ projectedStress (sourceDilation G.map σ) x i -
            cubeStress n i) ≤ C * σ := by
  obtain ⟨U, hU, hKU, σ₀, hσ₀, hσ₁, hseg, hgeom, hb⟩ :=
    exists_projectedStress_dilation_bounds G hK
  obtain ⟨C, hC, hbound⟩ := hb 6
  let σ := min σ₀ (ε / (2 * C))
  have hσ : 0 < σ := lt_min hσ₀ (by positivity)
  have hσσ₀ : σ ≤ σ₀ := min_le_left _ _
  have hsmall : C * σ < ε := by
    have := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp
      (show σ ≤ ε / (2 * C) from min_le_right _ _)
    nlinarith
  obtain ⟨hi, hr, hsmooth⟩ := hgeom σ ⟨hσ, hσσ₀⟩
  refine ⟨σ, hσ, hσσ₀.trans hσ₁, U, hU, hKU,
    hseg σ ⟨hσ.le, hσσ₀⟩, hi, hr, hsmooth,
    fun i ↦ (hbound σ ⟨hσ, hσσ₀⟩ i).trans_lt hsmall, ?_⟩
  intro r
  obtain ⟨Cᵣ, hCᵣ, hbᵣ⟩ := hb r
  exact ⟨Cᵣ, hCᵣ, hbᵣ σ ⟨hσ, hσσ₀⟩⟩

/-- The stress-frame part of fixed reference initialization
(`main:prop:seed`, `main:eq:normalized`, `app:ch_seed:setup:seed-current`),
with the analytic reference actually constructed by
`exists_analytic_flatReference`. There are no remaining analytic input
hypotheses. The only requested smallness is the fixed low reference threshold;
this does not construct carrier phases or their quantitative gaps. -/
theorem exists_analytic_reference_with_small_projectedStress (hn : 5 ≤ n)
    {K : Set (Euclidean n)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : FlatReference n, AnalyticOnNhd ℝ G.map Set.univ ∧
      ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ sourceDilation G.map σ 0 = 0 ∧
        (∀ x, inducedMetric (sourceDilation G.map σ) x = 1) ∧
        ∃ U : Set (Euclidean n), IsOpen U ∧ K ⊆ U ∧
          (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ U, t • (σ • x) ∈ G.domain.chart n) ∧
          IsImmersionOn (sourceDilation G.map σ) U ∧
          HasFullNormalRankOn (sourceDilation G.map σ) U ∧
          (∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress (sourceDilation G.map σ) x i) U) ∧
          (∀ i, cNorm K 6 (fun x ↦ projectedStress (sourceDilation G.map σ) x i -
            cubeStress n i) < ε) ∧
          ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i,
            cNorm K r (fun x ↦ projectedStress (sourceDilation G.map σ) x i -
              cubeStress n i) ≤ C * σ := by
  obtain ⟨G, hG⟩ := exists_analytic_flatReference hn
  obtain ⟨σ, hσ, hσ₁, hrest⟩ := exists_source_scale_projectedStress_lt G hK hε
  exact ⟨G, hG, σ, hσ, hσ₁, sourceDilation_zero G.map_zero,
    inducedMetric_sourceDilation_eq_one hσ G.contDiff G.inducedMetric_eq_one, hrest⟩

end JanetCartan.ProjectedStressFrame
