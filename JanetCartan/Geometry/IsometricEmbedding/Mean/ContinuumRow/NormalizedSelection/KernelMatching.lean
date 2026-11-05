module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedScalarMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedCoefficients

/-!
# Literal kernels of the retained source-normalized carriers

The scalar transport supplied by the common initializer is retained. On its
common working cylinder, source-flow matching identifies the actual canonical
carrier with `FrozenModel.normalizedCarrierData`. The equality is proved for
the entire supported kernel, including both masks, before integration against
the original carrier measure. Consumers are the normalized row selection and
the same-row normal comparison in `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection

open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier
open ContinuumNormal.FrozenModel ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
open NormalizedBackground NormalizedBackground.SourceGeometry
open NullTransport NullTransport.ActualFlow NullTransport.FlowAmplitude HamiltonPhase

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp q, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
    (row col : Fin n)
    (Φ₀ Y₀ Φσ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) →
      Euclidean (n - 1) × Euclidean 3)
    (initial₀ initialσ : Euclidean (n - 1) × Euclidean 3 → ℝ)

include hF hrank hphysical hseed htrans hσ hσ1 hscaled in
/-- The same retained phase, scalar and stress yield every literal source
coefficient, with arbitrary supplied initial scalars (`new:lem:scaling`). -/
private theorem source_carrier_fields {c C : ℝ} (hP : P.IsValid c C)
    {x : Euclidean n} {z : CarrierParameter}
    (hx : x ∈ ball 0 T.physicalRadius)
    (hz : parameter z ∈ parameterInterior (2 * P.radius))
    (hscalar : carrierScalarAmplitude T Qσ (sourceDilation F σ) row col Φσ Yσ
        initialσ (x, parameter z) =
      sourceAmplitude (carrierScalarAmplitude T Q₀ F row col Φ₀ Y₀ initial₀)
        σ (x, parameter z)) :
    transportPosition T Qσ (x, z) = normalizedTransportPosition T Q₀ σ (x, z) ∧
    T.carrierGradient Qσ x (parameter z) = normalizedCovector T Q₀ σ x z ∧
    normalField T Qσ (sourceDilation F σ) row col Φσ Yσ initialσ x z =
      normalizedNormal T Q₀ F row col Φ₀ Y₀ initial₀ σ x z ∧
    Qσ.1 x = Q₀.1 (σ • x) := by
  have hz' : parameter z ∈ parameterCube (2 * P.radius) := fun i ↦ (hz i).le
  have hsx := (convex_ball (0 : Euclidean n) T.physicalRadius).smul_mem_of_zero_mem
    (mem_ball_self T.physicalRadius_pos) hx ⟨hσ.le, hσ1⟩
  have hxU : σ • x ∈ U :=
    (carrierPhase_gradient_mem_domain (T.currentChart Q₀) T.reference.spatialPatch
      (T.target_contains_closed hsx hz')).1
  have hgrad := current_carrierGradient_source_dilation T Q₀ Qσ hF hrank
    hphysical hseed htrans hσ hσ1 hscaled hx hz'
  have hnull := current_carrierNullvector_source_dilation T Q₀ Qσ hF hrank
    hphysical hseed htrans hσ hσ1 hscaled col hx hz'
  refine ⟨?_, hgrad.trans
    (normalizedCovector_eq_retainedCarrierGradient T Q₀ hP hsx hz).symm, ?_, ?_⟩
  · exact (current_transportPosition_source_dilation_on_patch T Q₀ Qσ hF hrank
      hphysical hseed htrans hσ hσ1 hscaled).1 ⟨hx, hz⟩
  · rw [normalizedNormal_eq_sourceDilation T Q₀ F row col Φ₀ Y₀ initial₀
      hσ hF x z (hrank _ hxU)]
    simp only [normalField, hgrad, hnull, hscalar, sourceAmplitude, smul_smul,
      smul_eq_mul]
  · rw [hscaled, hseed]
    exact funext (ProjectedStressFrame.projectedStress_sourceDilation hσ hF x (hrank _ hxU))

include hF hrank hphysical hseed htrans hσ hσ1 hscaled in
/-- The actual supported carrier kernel is the literal normalized seed kernel
once the retained scalar's source-flow identity is supplied. That identity is
the output of `exists_retained_scalar_source_flows`, with the original seed
scalar; no kernel or operator equality is assumed. Masks, the chart, both
quadratures and the carrier measure are unchanged (`app:ch_background:eq:bg-T`,
`app:ch_background:eq:bg-Nsigma`, `new:lem:scaling`). -/
theorem carrierKernel_eq_normalized_of_scalar_transport {c C : ℝ} (hP : P.IsValid c C)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {W : Set (Euclidean n × Euclidean 3)}
    (hW : W ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius))
    (hsupport : ∀ (x : Torus n) (z : CarrierParameter) (η : Euclidean (n - 1)),
      FixedCutoffs.periodic hr hcell 1 x ≠ 0 → angular z η ≠ 0 →
      (AmplitudeBound.centeredTorusRepresentative x, parameter z) ∈ W)
    (hscalar : EqOn
      (carrierScalarAmplitude T Qσ (sourceDilation F σ) row col Φσ Yσ initialσ)
      (sourceAmplitude (carrierScalarAmplitude T Q₀ F row col Φ₀ Y₀ initial₀) σ) W) :
    carrierKernel (data T Qσ (sourceDilation F σ) row col Φσ Yσ initialσ
      hr hcell angular high) =
    carrierKernel (normalizedCarrierData T Q₀ F row col Φ₀ Y₀ initial₀
      hr hcell angular high σ) := by
  funext x u
  by_cases hx : x ∈ PeriodicLocalL2.torusChart (closedBall (0 : Euclidean n) (4 * r))
  · simp only [carrierKernel, normalizedCarrierData, data, hx, indicator_of_mem]
    by_cases hm : FixedCutoffs.periodic hr hcell 1 x = 0
    · simp only [carrierAmplitude, hm, zero_mul, zero_smul, map_zero, smul_zero]
    by_cases ha : angular u.1 (‖u.2‖⁻¹ • u.2) = 0
    · simp only [carrierAmplitude, ha, mul_zero, zero_mul, zero_smul, map_zero, smul_zero]
    have hp := hsupport x u.1 (‖u.2‖⁻¹ • u.2) hm ha
    obtain ⟨ht, hg, hn, hq⟩ := source_carrier_fields T Q₀ Qσ hF hrank hphysical
      hseed htrans hσ hσ1 hscaled row col Φ₀ Y₀ Φσ Yσ initial₀ initialσ hP
      (hW hp).1 (hW hp).2 (hscalar hp)
    simp only [carrierPhase, carrierAmplitude, reducedCovector, ht, hg, hn, hq]
  · simp [carrierKernel, data, normalizedCarrierData, hx]

end JanetCartan.ContinuumRow.NormalizedSelection
