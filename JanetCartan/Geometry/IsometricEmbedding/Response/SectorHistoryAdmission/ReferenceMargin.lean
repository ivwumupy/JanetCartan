module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SectorHistoryAdmission.CoefficientCap

/-!
# The original full-array margin supplies frame-component admission

Extract the principal coefficients of the same initialized reference, with
their actual Frobenius norms. This connects the original initializer's finite
full-array continuation to the existing retained-history range and C6 admission
producer. Sources: `app:ch_waves:eq:reduced-symbol`,
`app:ch_seed:setup:seed-current`, and `app:ch_regular:eq:coefficient-extension`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.SectorHistoryAdmission
open GeometricProfile ProtectedFlow ResponseTransfer.RetainedFactors
open FullPhaseCharts.InverseEstimates ProjectedStressFrame ContinuumRow.ImageGeometry
open CurrentGeometricNeighborhood

/-- The reference's frame-component error is a literal linear projection of
its full reduced-array error, on a neighborhood of the ORIGINAL closed ball.
This supplies the reference premise of
`exists_reference_tolerance_for_retained_history_admission` from the original
initializer (`app:ch_waves:eq:reduced-symbol`, `app:ch_seed:setup:seed-current`). -/
theorem cNorm_reference_frame_component_sub_le_full_array {n : ℕ}
    (G : FlatReference n) {r R : ℝ} (hrR : r < R)
    (hR : R < G.domain.chartRadius) (m : ℕ) (i : Fin n) :
    cNorm (closedBall (0 : Euclidean n) r) m
      (fun x ↦ projectedStress G.map x i - cubeStress n i) ≤
      ‖(ContinuousLinearMap.proj i).comp (reducedFrameProjection n)‖ *
        cNorm (closedBall (0 : Euclidean n) r) m
          (geometricReducedCoefficients G.map -
            reducedCoefficientBackground (fun _ _ ↦ 0)) := by
  let L := (ContinuousLinearMap.proj i).comp (reducedFrameProjection n)
  let a := geometricReducedCoefficients G.map - reducedCoefficientBackground (fun _ _ ↦ 0)
  have hraw := contDiffOn_geometricReducedCoefficients G.contDiff isOpen_ball
    (fun x _ ↦ reference_isImmersion G x)
    (fun x hx ↦ G.fullNormalRank x (ball_subset_ball hR.le hx))
  have ha : ∀ x ∈ closedBall (0 : Euclidean n) r, ContDiffAt ℝ m a x := by
    intro x hx
    exact ((hraw.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hrR hx))).sub
      (contDiff_reducedCoefficientBackground contDiff_const).contDiffAt).of_le (by simp)
  have heq : cNorm (closedBall (0 : Euclidean n) r) m (L ∘ a) =
      cNorm (closedBall (0 : Euclidean n) r) m
        (fun x ↦ projectedStress G.map x i - cubeStress n i) := by
    apply cNorm_eq_of_eventuallyEq _ m
    intro x hx
    filter_upwards [isOpen_ball.mem_nhds (closedBall_subset_ball hrR hx)] with y hy
    change (StressFrame.geometricCubeStress G.map y i).val - cubeStress n i =
      projectedStress G.map y i - cubeStress n i
    rw [geometricCubeStress_val_eq_projectedStress
      (G.contDiff.contDiffAt.of_le (by simp))
      (G.fullNormalRank y (ball_subset_ball hR.le hy))]
  rw [← heq]
  exact cNorm_postLinear_le_on (isCompact_closedBall _ _) m L ha

/-- A full-array tolerance BEFORE the reference forces every required frame
component tolerance, at the same order and on the same closed ball. The full
zeroth coefficient stays in the array; no replacement background is used.
The consumer is the combined same-history sector admission below
(`app:ch_seed:setup:seed-current`, `main:prop:seed`). -/
theorem exists_full_array_tolerance_for_reference_frame_components {n : ℕ}
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ G : FlatReference n, ∀ r R : ℝ,
      r < R → R < G.domain.chartRadius →
      cNorm (closedBall (0 : Euclidean n) r) m
        (geometricReducedCoefficients G.map -
          reducedCoefficientBackground (fun _ _ ↦ 0)) < η →
      ∀ i, cNorm (closedBall (0 : Euclidean n) r) m
        (fun x ↦ projectedStress G.map x i - cubeStress n i) < ε := by
  let L := fun i : Fin n ↦ (ContinuousLinearMap.proj i).comp (reducedFrameProjection n)
  let C : ℝ := 1 + ∑ i, ‖L i‖
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ε / C, div_pos hε hC, ?_⟩
  intro G r R hrR hR href i
  have hLi : ‖L i‖ ≤ C := by
    have hsum := Finset.single_le_sum (s := Finset.univ) (f := fun j ↦ ‖L j‖)
      (fun j _ ↦ norm_nonneg _) (Finset.mem_univ i)
    dsimp only [C]
    linarith
  calc
    _ ≤ ‖L i‖ * cNorm (closedBall (0 : Euclidean n) r) m
        (geometricReducedCoefficients G.map - reducedCoefficientBackground (fun _ _ ↦ 0)) :=
      cNorm_reference_frame_component_sub_le_full_array G hrR hR m i
    _ ≤ C * cNorm (closedBall (0 : Euclidean n) r) m
        (geometricReducedCoefficients G.map - reducedCoefficientBackground (fun _ _ ↦ 0)) :=
      mul_le_mul_of_nonneg_right hLi (cNorm_nonneg _ _ _)
    _ < C * (ε / C) := mul_lt_mul_of_pos_left href hC
    _ = ε := mul_div_cancel₀ ε hC.ne'

end JanetCartan.SectorHistoryAdmission
