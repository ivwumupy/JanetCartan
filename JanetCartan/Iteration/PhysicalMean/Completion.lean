module

public import JanetCartan.Iteration.PhysicalGeometry.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PhysicalCompletion
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.ProjectedResidualBound

/-!
# The full physical error of the same normal completion

For `new:lem:mean-exact`, the genuine revised Schwartz history supplies the
immersion, rank, frame and inverse-Gram constant.  The remaining reduced
residual belongs to the fixed-source iteration, not to a different prepared
run.  The target can be literally `PhysicalSmoothing.normalizedSource`.

This is the geometric error transfer consumed by `RevisedStage` after the
actual sampled source iteration.  It does not assume a full mean-error bound
or claim that the original canonical operators have yet been instantiated.
-/

@[expose] public noncomputable section

open Set Metric Finset
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalMean

open CurrentMean ProjectedStressFrame RawPrimary UniformStep

/-- `new:eq:qT-identity`: contractions of the literal uncompleted defect,
with the full target, full strain, full sampled self tensor, and original sign. -/
def reducedPhysicalResidual {n N : ℕ} (F W : Euclidean n → Euclidean N)
    (target H : MetricField n) : Euclidean n → Euclidean n :=
  fun x ↦ WithLp.toLp 2 (fun i ↦ tensorPairing (projectedStress F x i)
    (target x - linearizedMetric F W x - H x))

/-- `new:eq:mean-error-formula`: actual physical admissibility discharges
all geometric hypotheses and the reconstruction constant, before every source,
sampled self tensor and precision.  Only the lower reduced residual remains
for the fixed-source Picard producer; no final mean estimate is assumed. -/
theorem exists_history_completedMean_error_transfer {n : ℕ} (hn : 5 ≤ n)
    (G : FlatReference n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hR : R < G.domain.chartRadius) {B : ℝ} (hB : 1 ≤ B)
    {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ))
    (hreference : ∀ i, cNorm (closedBall (0 : Euclidean n) r) 6
      (fun x ↦ projectedStress G.map x i - cubeStress n i) <
        ambientStrainFrameThreshold hn / 2) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      ∀ (W : Euclidean n → Euclidean (embeddingDimension n)) (target H : MetricField n),
      ContDiffOn ℝ ∞ W (ball 0 R) → ContDiffOn ℝ ∞ target (ball 0 R) →
      ContDiffOn ℝ ∞ H (ball 0 R) →
      let F := RevisedGlobal.finiteMap G.map u
      ContDiffOn ℝ ∞ (completedMeanField F W target H) (ball 0 R) ∧
      ∀ x ∈ closedBall (0 : Euclidean n) r,
        (target x).IsSymm → (H x).IsSymm →
        ‖linearizedMetric F (completedMeanField F W target H) x + H x - target x‖ ≤
          projectedStressResidualConstant hn * ‖reducedPhysicalResidual F W target H x‖ := by
  obtain ⟨S, hS, _, _, _, _, hhistory⟩ :=
    PhysicalGeometry.exists_cube_frame_neighborhood G hr hrR hR hB hStar horder
      (ambientStrainFrameThreshold_pos hn) hreference
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ j u ell hu W target H hW ht hH F
  have hF : ContDiff ℝ ∞ F := G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  obtain ⟨hi, hrank, _, _, _, _, hclose⟩ := hhistory R₀ hR₀ j u ell hu
  have hKU : closedBall (0 : Euclidean n) r ⊆ ball 0 R := closedBall_subset_ball hrR
  refine ⟨contDiffOn_completedMeanField isOpen_ball hF.contDiffOn hW ht hH hi hrank, ?_⟩
  intro x hx hts hHs
  have hframe := projectedStress_tensorFrame_of_cNorm_closeness hn isOpen_ball
    (isCompact_closedBall _ _) hKU hF.contDiffOn hi hrank hclose hx
  have hcoef := projectedStress_residual_coefficient_le hn isOpen_ball
    (isCompact_closedBall _ _) hKU hF.contDiffOn hi hrank hclose hx
  have hnonneg : 0 ≤ ∑ a, ∑ b, |(stressGram (projectedStress F x))⁻¹ a b| *
      ‖projectedStress F x a‖ := sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ by positivity
  have hcoef' : (∑ a, ∑ b, |(stressGram (projectedStress F x))⁻¹ a b| *
      ‖projectedStress F x a‖) ≤ projectedStressResidualConstant hn := by linarith
  have hcomp (i : Fin n) : |tensorPairing (projectedStress F x i)
      (target x - linearizedMetric F W x - H x)| ≤
        ‖reducedPhysicalResidual F W target H x‖ :=
    PiLp.norm_apply_le (reducedPhysicalResidual F W target H x) i
  calc
    _ ≤ ∑ a, ∑ b, |(stressGram (projectedStress F x))⁻¹ a b| *
        |tensorPairing (projectedStress F x b)
          (target x - linearizedMetric F W x - H x)| * ‖projectedStress F x a‖ :=
      completedMeanField_error_norm_le isOpen_ball hF.contDiffOn hW ht hH hi hrank
        (hKU hx) hts hHs hframe.2.1 hframe.2.2
    _ ≤ ∑ a, ∑ b, (|(stressGram (projectedStress F x))⁻¹ a b| *
        ‖projectedStress F x a‖) * ‖reducedPhysicalResidual F W target H x‖ := by
      apply sum_le_sum
      intro a _
      apply sum_le_sum
      intro b _
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcomp b) (abs_nonneg _)) (norm_nonneg _)).trans_eq (by ring)
    _ = (∑ a, ∑ b, |(stressGram (projectedStress F x))⁻¹ a b| *
        ‖projectedStress F x a‖) * ‖reducedPhysicalResidual F W target H x‖ := by
      simp only [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef' (norm_nonneg _)

end JanetCartan.PhysicalMean
