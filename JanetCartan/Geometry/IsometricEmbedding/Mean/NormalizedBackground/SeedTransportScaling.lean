module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.AdaptedCoefficients

/-!
# Transport of the constructed seed amplitude under source dilation

The actual retained left null row, projected frame and physical covector are
used in the scaled equation. `ConstructedSeedMatching` supplies the input
amplitude from its positive unit transport and instantiates this deduction
(`app:ch_background:eq:bg-Nsigma`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground
open ActualCarriers FrozenMenu CurrentFullPhase HamiltonPhase ProjectedStressFrame
open SourceGeometry NullTransport
open ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching

/-- The SAME nonzero unit-transport amplitude solves the literal scaled
pencil and reduced transport equations. Seed regularity, nullity and the
left-row equation are the outputs of `exists_refined_flat_seed_unit_transports`;
`exists_constructed_flat_seed_matched_mean` supplies them below. The scaled
equation is derived using `reducedOperator_sourceAmplitude` and the actual
retained conullvector, with no coordinate-direction replacement
(`app:ch_background:eq:bg-Nsigma`). -/
theorem retained_sourceAmplitude_transport {n : ℕ} (G : FlatReference n)
    {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (hUG : U ⊆ G.domain.chart n) (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = projectedStress G.map)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp q, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = projectedStress (sourceDilation G.map σ))
    (row : Fin n) {x : Euclidean n} (hx : x ∈ ball 0 T.physicalRadius)
    {z : Euclidean 3} (hz : z ∈ parameterCube (2 * P.radius))
    {b : Euclidean n × Euclidean 3 → Euclidean n}
    (hb : ContDiffAt ℝ ∞ b (σ • x, z)) (hne : b (σ • x, z) ≠ 0)
    (hnull : reducedSymbol (Q₀.1 (σ • x)) (T.carrierGradient Q₀ (σ • x) z) *ᵥ
      (fun j ↦ b (σ • x, z) j) = 0)
    (htransport : carrierConullvector T Q₀ row (σ • x, z) ⬝ᵥ
      reducedOperator G.map Q₀.1 (fun y ↦ b (y, z)) (σ • x) = 0) :
    sourceAmplitude b σ (x, z) ≠ 0 ∧
      reducedSymbol (Qσ.1 x) (T.carrierGradient Qσ x z) *ᵥ
        (fun j ↦ sourceAmplitude b σ (x, z) j) = 0 ∧
      carrierConullvector T Qσ row (x, z) ⬝ᵥ
        reducedOperator (sourceDilation G.map σ) Qσ.1
          (fun y ↦ sourceAmplitude b σ (y, z)) x = 0 := by
  have hrank : HasFullNormalRankOn G.map U := fun y hy ↦ G.fullNormalRank y (hUG hy)
  have hsx := (convex_ball (0 : Euclidean n) T.physicalRadius).smul_mem_of_zero_mem
    (mem_ball_self T.physicalRadius_pos) hx ⟨hσ.le, hσ1⟩
  have hxU := (carrierPhase_gradient_mem_domain (T.currentChart Q₀) T.reference.spatialPatch
    (T.target_contains_closed hsx hz)).1
  have hframe : Qσ.1 x = Q₀.1 (σ • x) := by
    rw [hseed, hscaled]
    exact funext (projectedStress_sourceDilation hσ G.contDiff x (hrank _ hxU))
  refine ⟨smul_ne_zero hσ.ne' hne, ?_, ?_⟩
  · rw [hframe, current_carrierGradient_source_dilation T Q₀ Qσ G.contDiff hrank
      hphysical hseed htrans hσ hσ1 hscaled hx hz]
    change reducedSymbol _ _ *ᵥ (σ • (fun j ↦ b (σ • x, z) j)) = 0
    rw [Matrix.mulVec_smul, hnull, smul_zero]
  · have hb' (j : Fin n) : DifferentiableAt ℝ (fun y ↦ b (y, z) j) (σ • x) :=
      ((contDiffAt_piLp 2).mp (hb.comp (σ • x)
        (contDiffAt_id.prodMk contDiffAt_const)) j).differentiableAt (by simp)
    rw [current_carrierConullvector_source_dilation T Q₀ Qσ G.contDiff hrank
      hphysical hseed htrans hσ hσ1 hscaled row hx hz, hscaled,
      reducedOperator_sourceAmplitude hU G.contDiff (fun y _ ↦ G.inducedMetric_eq_one y)
        hσ hxU (hrank _ hxU) hb', ← hseed, dotProduct_smul, htransport, smul_zero]

end JanetCartan.NormalizedBackground
