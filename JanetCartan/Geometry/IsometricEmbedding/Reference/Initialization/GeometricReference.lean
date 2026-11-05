module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.ScaledReference
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.CommonMargins
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.GeometricNeighborhood

/-!
# Fixing the source scale and the geometric neighborhood

For `main:prop:seed`, source scaling actually supplies the cube-frame tolerance
required by the C8 neighborhood theorem. The reference, positive normal gap,
low bound and neighborhood are all fixed before the target or its accuracy.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan
open ProjectedStressFrame CurrentGeometricNeighborhood GeometricProfile ProtectedFlow

/-- Choose the source scale from a prescribed carrier-frame threshold, then
derive the actual geometric neighborhood (`main:prop:seed`,
`app:ch_seed:setup:seed-current`). The full local and extended arrays meet
their fixed finite margins at this same scale
(`app:ch_regular:eq:coefficient-extension`). The consumer constructs `G₀` analytically
before choosing the carrier family and its threshold. No metric gap, normal
gap or current-frame comparison is assumed. -/
theorem exists_scaled_reference_geometric_neighborhood_with_full_margins {n : ℕ} (G₀ : FlatReference n)
    {b R : ℝ} (hb : 0 < b) (hbR : b < R) (hR : R < G₀.domain.chartRadius)
    {ε : ℝ} (hε : 0 < ε)
    (p : BallExtension.Parameters (Euclidean n))
    (orders : Finset ℕ) (margin extendedMargin : ℕ → ℝ)
    (hmargin : ∀ j ∈ orders, 0 < margin j)
    (hextendedMargin : ∀ j ∈ orders, 0 < extendedMargin j)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < cap ∧ ρ ≤ 1 ∧
      ∃ G : FlatReference n, G.domain = G₀.domain ∧ G.map = sourceDilation G₀.map ρ ∧
        (∀ j ∈ orders, cNorm (closedBall (0 : Euclidean n) b) j
          (geometricReducedCoefficients G.map -
            reducedCoefficientBackground (fun _ _ ↦ 0)) < margin j) ∧
        ContDiff ℝ ∞ (extendedReducedCoefficients p (fun _ _ ↦ 0) G.map) ∧
        (∀ j ∈ orders, cNorm univ j
          (extendedReducedCoefficients p (fun _ _ ↦ 0) G.map -
            reducedCoefficientBackground (fun _ _ ↦ 0)) < extendedMargin j) ∧
        (∀ i, cNorm (closedBall (0 : Euclidean n) b) 6
          (fun x ↦ projectedStress G.map x i - cubeStress n i) < ε / 2) ∧
        ∃ δ C₀ κ : ℝ, 0 < δ ∧ 0 < C₀ ∧ 0 < κ ∧
          ∀ (U : Set (Euclidean n)) (F : Euclidean n → Euclidean (embeddingDimension n)),
            IsOpen U → closedBall 0 R ⊆ U → ContDiffOn ℝ ∞ F U →
            cNorm (closedBall 0 R) 8 (F - G.map) < δ →
            IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
            cNorm (closedBall 0 b) 4 F ≤ C₀ ∧
            (∀ x ∈ ball 0 R, ∀ v,
              (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
            (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
              κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
            (∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress F x i) (ball 0 R)) ∧
            ∀ i, cNorm (closedBall 0 b) 6
              (fun x ↦ projectedStress F x i - cubeStress n i) < ε := by
  obtain ⟨ρ, hρ, hρcap, hρ1, hfull, hclose, hsmooth, hextended⟩ :=
    ReferenceInitialization.CommonMargins.exists_source_scale_full_and_extended_margins G₀
      (isCompact_closedBall (0 : Euclidean n) b) p orders margin extendedMargin
      hmargin hextendedMargin (half_pos hε) hcap
  let G := sourceDilationReference G₀ hρ hρ1
  have hR' : R < G.domain.chartRadius := hR
  obtain ⟨δ, hδ, C₀, hC₀, κ, hκ, hnear⟩ :=
    exists_cube_frame_neighborhood G hb hbR hR' hε hclose
  exact ⟨ρ, hρ, hρcap, hρ1, G, rfl, rfl, hfull, hsmooth, hextended, hclose,
    δ, C₀, κ, hδ, hC₀, hκ, hnear⟩

/-- Choose the source scale from a prescribed carrier-frame threshold, then
derive the actual geometric neighborhood (`main:prop:seed`,
`app:ch_seed:setup:seed-current`). The consumer constructs `G₀` analytically
before choosing the carrier family and its threshold. No metric gap, normal
gap or current-frame comparison is assumed. -/
theorem exists_scaled_reference_geometric_neighborhood {n : ℕ} (G₀ : FlatReference n)
    {b R : ℝ} (hb : 0 < b) (hbR : b < R) (hR : R < G₀.domain.chartRadius)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∃ G : FlatReference n, G.domain = G₀.domain ∧ G.map = sourceDilation G₀.map ρ ∧
        (∀ i, cNorm (closedBall (0 : Euclidean n) b) 6
          (fun x ↦ projectedStress G.map x i - cubeStress n i) < ε / 2) ∧
        ∃ δ C₀ κ : ℝ, 0 < δ ∧ 0 < C₀ ∧ 0 < κ ∧
          ∀ (U : Set (Euclidean n)) (F : Euclidean n → Euclidean (embeddingDimension n)),
            IsOpen U → closedBall 0 R ⊆ U → ContDiffOn ℝ ∞ F U →
            cNorm (closedBall 0 R) 8 (F - G.map) < δ →
            IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
            cNorm (closedBall 0 b) 4 F ≤ C₀ ∧
            (∀ x ∈ ball 0 R, ∀ v,
              (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
            (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
              κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
            (∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress F x i) (ball 0 R)) ∧
            ∀ i, cNorm (closedBall 0 b) 6
              (fun x ↦ projectedStress F x i - cubeStress n i) < ε := by
  let p : BallExtension.Parameters (Euclidean n) :=
    ⟨0, 1, by norm_num, 1 / 4, by norm_num, by norm_num⟩
  obtain ⟨ρ, hρ, _, hρ1, G, hdomain, hmap, _, _, _, hclose, hnear⟩ :=
    exists_scaled_reference_geometric_neighborhood_with_full_margins G₀ hb hbR hR hε
      p ∅ (fun _ ↦ 1) (fun _ ↦ 1) (by simp) (by simp) (by norm_num : (0 : ℝ) < 1)
  exact ⟨ρ, hρ, hρ1, G, hdomain, hmap, hclose, hnear⟩

end JanetCartan
