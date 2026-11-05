module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.StressScaling
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.IterationInput

/-!
# The source-scaled reference and the initial iteration inputs

The reference/initial-target half of `main:prop:seed`, `main:eq:normalized`, and
`main:eq:seed-small`. We construct an analytic flat reference, choose its source
scale from a prescribed positive low stress threshold, and package the actual
dilated map as a `FlatReference` on the same domain. Only then do we quantify over
the target metric and choose its normalization and common parameter interval.

The last two conclusions of `exists_scaled_reference_iteration_inputs` are the
`htarget` and `hinitial` inputs of
`UniformHistoryCorrection.exists_local_embedding_of_initial_defects`. No analytic
existence hypothesis is required here. The parent construction must still supply
the actual carrier neighborhood, uniform quantitative gaps for perturbations, and
`UniformHistoryCorrection` on this same reference, core, and target family. This
module does not prove the complete initialization proposition or local existence.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan

/-- `main:eq:normalized` and `app:ch_seed:cor:seed-uniform-dilation`: a positive
source contraction of a flat reference is a flat reference on its original
domain. This packages the exact geometric scaling identities for the initial
target adapter, without assuming any geometric properties of the scaled map. -/
def sourceDilationReference {n : ℕ} (G : FlatReference n)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) : FlatReference n where
  domain := G.domain
  map := sourceDilation G.map ρ
  contDiff := contDiff_sourceDilation G.contDiff
  map_zero := sourceDilation_zero G.map_zero
  inducedMetric_eq_one := inducedMetric_sourceDilation_eq_one hρ G.contDiff
    G.inducedMetric_eq_one
  fullNormalRank := by
    apply (hasFullNormalRankOn_sourceDilation_iff hρ G.contDiff (G.domain.chart n)).mpr
    rintro _ ⟨x, hx, rfl⟩
    apply G.fullNormalRank
    have hx' : ‖x‖ < G.domain.chartRadius := by
      simpa only [LocalDomain.chart, Metric.mem_ball, dist_zero_right] using hx
    change dist (ρ • x) 0 < G.domain.chartRadius
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg hρ.le]
    exact (mul_le_of_le_one_left (norm_nonneg x) hρ₁).trans_lt hx'
  stressSpace_zero := by
    rw [stressSpace_sourceDilation hρ G.contDiff, smul_zero]
    exact G.stressSpace_zero

/-- The construction chart is unchanged in `main:eq:normalized`. -/
@[simp] theorem sourceDilationReference_domain {n : ℕ} (G : FlatReference n)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    (sourceDilationReference G hρ hρ₁).domain = G.domain := rfl

/-- The packaged map is the actual source dilation of `main:eq:normalized`. -/
@[simp] theorem sourceDilationReference_map {n : ℕ} (G : FlatReference n)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    (sourceDilationReference G hρ hρ₁).map = sourceDilation G.map ρ := rfl

/-- The reference half of `main:prop:seed`: construct the analytic reference
first, then fix its source scale from the low `C⁶` stress threshold on its closed
chart. The resulting flat reference has the exact dilated map and original
domain. The open neighborhood, immersion, full normal rank, and stress estimates
are actual conclusions. No target metric or later accuracy enters this choice.
Carrier constructions and quantitative gaps for perturbed references remain
separate obligations of the complete initialization proposition. -/
theorem exists_scaled_flatReference {n : ℕ} (hn : 5 ≤ n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G₀ : FlatReference n, AnalyticOnNhd ℝ G₀.map Set.univ ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
        ∃ Gref : FlatReference n, Gref.domain = G₀.domain ∧
          Gref.map = sourceDilation G₀.map ρ ∧
          ∃ U : Set (Euclidean n), IsOpen U ∧ Gref.domain.closureChart n ⊆ U ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ U, t • (ρ • x) ∈ G₀.domain.chart n) ∧
            IsImmersionOn Gref.map U ∧ HasFullNormalRankOn Gref.map U ∧
            (∀ i, ContDiffOn ℝ ∞ (fun x ↦ ProjectedStressFrame.projectedStress
              Gref.map x i) U) ∧
            (∀ i, cNorm (Gref.domain.closureChart n) 6
              (fun x ↦ ProjectedStressFrame.projectedStress Gref.map x i -
                cubeStress n i) < ε) ∧
            ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i,
              cNorm (Gref.domain.closureChart n) r
                (fun x ↦ ProjectedStressFrame.projectedStress Gref.map x i -
                  cubeStress n i) ≤ C * ρ := by
  obtain ⟨G₀, hG₀⟩ := exists_analytic_flatReference hn
  obtain ⟨ρ, hρ, hρ₁, U, hU, hKU, hseg, himm, hrank, hsmooth, hlow, hhigh⟩ :=
    ProjectedStressFrame.exists_source_scale_projectedStress_lt G₀
      (isCompact_closedBall (0 : Euclidean n) G₀.domain.chartRadius) hε
  exact ⟨G₀, hG₀, ρ, hρ, hρ₁, sourceDilationReference G₀ hρ hρ₁, rfl, rfl,
    U, hU, hKU, hseg, himm, hrank, hsmooth, hlow, hhigh⟩

/-- `main:prop:seed`, `main:eq:normalized`, and `main:eq:seed-small`: construct
the source-scaled reference and then supply the exact normalized initial-target
inputs consumed by `UniformHistoryCorrection.exists_local_embedding_of_initial_defects`.
The reference, source scale, and stress neighborhood precede the target metric;
the coordinate normalization and common positive interval precede every initial
accuracy. All reference and initial-target inputs are constructed here. The
uniform history correction and its carrier/perturbation estimates are not
asserted and must still be proved by the parent construction. -/
theorem exists_scaled_reference_iteration_inputs {n : ℕ} (hn : 5 ≤ n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G₀ : FlatReference n, AnalyticOnNhd ℝ G₀.map Set.univ ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
        ∃ Gref : FlatReference n, Gref.domain = G₀.domain ∧
          Gref.map = sourceDilation G₀.map ρ ∧
          ∃ U : Set (Euclidean n), IsOpen U ∧ Gref.domain.closureChart n ⊆ U ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ U, t • (ρ • x) ∈ G₀.domain.chart n) ∧
            IsImmersionOn Gref.map U ∧ HasFullNormalRankOn Gref.map U ∧
            (∀ i, ContDiffOn ℝ ∞ (fun x ↦ ProjectedStressFrame.projectedStress
              Gref.map x i) U) ∧
            (∀ i, cNorm (Gref.domain.closureChart n) 6
              (fun x ↦ ProjectedStressFrame.projectedStress Gref.map x i -
                cubeStress n i) < ε) ∧
            (∀ r : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i,
              cNorm (Gref.domain.closureChart n) r
                (fun x ↦ ProjectedStressFrame.projectedStress Gref.map x i -
                  cubeStress n i) ≤ C * ρ) ∧
            ∀ (g : MetricField n) (V : Set (Euclidean n)),
              IsOpen V → (0 : Euclidean n) ∈ V → IsRiemannianMetricOn g V →
              ∃ A : MetricTensor n, IsUnit A ∧ coordinatePullback g A 0 = 1 ∧
                ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
                  ∃ W : Set (Euclidean n), IsOpen W ∧ (0 : Euclidean n) ∈ W ∧
                    W ⊆ Gref.domain.core n ∧
                    (∀ s, 0 < s → s ≤ s₀ →
                      ContinuousOn (scaledMetric (coordinatePullback g A) (s * ρ))
                        (Gref.domain.core n)) ∧
                    (∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ s₀ ∧
                      cNorm (Gref.domain.core n) 0
                        (inducedMetric Gref.map -
                          scaledMetric (coordinatePullback g A) (s * ρ)) ≤ η) := by
  obtain ⟨G₀, hG₀, ρ, hρ, hρ₁, Gref, hdomain, hmap, U, hU, hKU, hseg,
    himm, hrank, hsmooth, hlow, hhigh⟩ := exists_scaled_flatReference hn hε
  refine ⟨G₀, hG₀, ρ, hρ, hρ₁, Gref, hdomain, hmap, U, hU, hKU, hseg,
    himm, hrank, hsmooth, hlow, hhigh, ?_⟩
  intro g V hV h0 hg
  exact exists_normalized_iteration_inputs_for_reference Gref hρ hV h0 hg

end JanetCartan
