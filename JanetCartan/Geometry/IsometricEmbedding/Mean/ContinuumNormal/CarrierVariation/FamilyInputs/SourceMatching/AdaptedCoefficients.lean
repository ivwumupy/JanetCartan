module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.Coefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Transport

/-!
# Dilation of the actual adapted null-transport coefficients

The time denominator is the retained normal contraction, with no rotation of
the projected stress frame. These identities supply the scalar comparison in
`app:ch_background:eq:bg-Nsigma` and `paper-v2.tex`, `new:lem:scaling`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
open HamiltonPhase NormalizedBackground.SourceGeometry
open ActualCarriers CurrentFullPhase NullTransport

variable {n N : ℕ} {P : FrozenMenu.Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))

include hF hrank hphysical hseed htrans hσ hσ1 hscaled

omit hphysical htrans in
private theorem current_frame_source_dilation {x : Euclidean n}
    (hx : x ∈ ball 0 T.physicalRadius) {z : Euclidean 3}
    (hz : z ∈ FrozenMenu.parameterCube (2 * P.radius)) :
    Qσ.1 x = Q₀.1 (σ • x) := by
  have hsx := (convex_ball (0 : Euclidean n) T.physicalRadius).smul_mem_of_zero_mem
    (mem_ball_self T.physicalRadius_pos) hx ⟨hσ.le, hσ1⟩
  have hxU := (carrierPhase_gradient_mem_domain (T.currentChart Q₀) T.reference.spatialPatch
    (T.target_contains_closed hsx hz)).1
  rw [hseed, hscaled]
  exact funext (ProjectedStressFrame.projectedStress_sourceDilation hσ hF x (hrank _ hxU))

/-- The selected left adjugate row has the same source pullback as the
right column. Consumer: adapted scalar potential matching.
Source: `app:ch_background:eq:bg-Nsigma`. -/
theorem current_carrierConullvector_source_dilation (row : Fin n) {x : Euclidean n}
    (hx : x ∈ ball 0 T.physicalRadius) {z : Euclidean 3}
    (hz : z ∈ FrozenMenu.parameterCube (2 * P.radius)) :
    carrierConullvector T Qσ row (x, z) = carrierConullvector T Q₀ row (σ • x, z) := by
  rw [carrierConullvector, carrierConullvector,
    current_frame_source_dilation T Q₀ Qσ hF hrank hseed hσ hσ1 hscaled hx hz,
    current_carrierGradient_source_dilation T Q₀ Qσ hF hrank
      hphysical hseed htrans hσ hσ1 hscaled hx hz]

/-- Dilation preserves the actual adapted time denominator. In particular a
seed lower bound transfers without a scale factor. Consumer: the normalized
direction and potential below. Source: `app:ch_background:eq:bg-Nsigma`. -/
theorem current_carrierAdaptedDenominator_source_dilation (row col : Fin n)
    {x : Euclidean n} (hx : x ∈ ball 0 T.physicalRadius) {z : Euclidean 3}
    (hz : z ∈ FrozenMenu.parameterCube (2 * P.radius)) :
    carrierAdaptedDenominator T Qσ row col (x, z) =
      carrierAdaptedDenominator T Q₀ row col (σ • x, z) := by
  rw [carrierAdaptedDenominator, carrierAdaptedDenominator,
    current_frame_source_dilation T Q₀ Qσ hF hrank hseed hσ hσ1 hscaled hx hz,
    current_carrierGradient_source_dilation T Q₀ Qσ hF hrank
      hphysical hseed htrans hσ hσ1 hscaled hx hz]

/-- The direction in the retained adapted coordinates is the unweighted seed
pullback. This is the coefficient identity needed for ODE uniqueness; no flow
identity is assumed. Source: `app:ch_background:eq:bg-Nsigma`. -/
theorem current_carrierTransportDirection_source_dilation (row col : Fin n)
    {x : Euclidean n} (hx : x ∈ ball 0 T.physicalRadius) {z : Euclidean 3}
    (hz : z ∈ FrozenMenu.parameterCube (2 * P.radius)) :
    carrierTransportDirection T Qσ row col (x, z) =
      carrierTransportDirection T Q₀ row col (σ • x, z) := by
  simp only [carrierTransportDirection,
    current_frame_source_dilation T Q₀ Qσ hF hrank hseed hσ hσ1 hscaled hx hz,
    current_carrierConullvector_source_dilation T Q₀ Qσ hF hrank
      hphysical hseed htrans hσ hσ1 hscaled row hx hz,
    current_carrierNullvector_source_dilation T Q₀ Qσ hF hrank
      hphysical hseed htrans hσ hσ1 hscaled col hx hz,
    current_carrierAdaptedDenominator_source_dilation T Q₀ Qσ hF hrank
      hphysical hseed htrans hσ hσ1 hscaled row col hx hz]

omit hF hrank hphysical hseed htrans hσ hσ1 hscaled in
private theorem reducedOperator_eq_of_germ
    (G : Euclidean n → Euclidean N) (Q : Euclidean n → Fin n → MetricTensor n)
    {b c : Euclidean n → Euclidean n} {x : Euclidean n}
    (h : b =ᶠ[𝓝 x] c) : reducedOperator G Q b x = reducedOperator G Q c x := by
  have hd (j : Fin n) : (fun y ↦ b y j) =ᶠ[𝓝 x] (fun y ↦ c y j) :=
    h.mono fun _ hy ↦ congrArg (fun v : Euclidean n ↦ v j) hy
  have hs : symmCovariantDeriv G b x = symmCovariantDeriv G c x := by
    ext i j
    simp only [symmCovariantDeriv, partialDeriv]
    rw [(hd j).fderiv_eq, (hd i).fderiv_eq, h.eq_of_nhds]
  exact congrArg (fun A ↦ fun i ↦ tensorPairing (Q x i) A) hs

/-- The adapted scalar potential has exactly one factor of scale. The flat
seed equation is the manuscript's genuine seed input; seed kernel regularity
is supplied by `exists_projected_null_coefficients` (or its local amplitude
constructor). The proof differentiates the matched kernel on an open ball
and uses `SourceGeometry.Transport` for the literal reduced operator.
Consumer: characteristic integral comparison. Source: `new:lem:scaling`. -/
theorem current_carrierTransportPotential_source_dilation
    (hflat : ∀ y ∈ U, inducedMetric F y = 1) (row col : Fin n)
    {x : Euclidean n} (hx : x ∈ ball 0 T.physicalRadius) {z : Euclidean 3}
    (hz : z ∈ FrozenMenu.parameterCube (2 * P.radius))
    (hk : ∀ j, DifferentiableAt ℝ
      (fun y ↦ carrierNullvector T Q₀ col (y, z) j) (σ • x)) :
    carrierTransportPotential T Qσ (sourceDilation F σ) row col (x, z) =
      σ * carrierTransportPotential T Q₀ F row col (σ • x, z) := by
  have hsx := (convex_ball (0 : Euclidean n) T.physicalRadius).smul_mem_of_zero_mem
    (mem_ball_self T.physicalRadius_pos) hx ⟨hσ.le, hσ1⟩
  have hxU := (carrierPhase_gradient_mem_domain (T.currentChart Q₀) T.reference.spatialPatch
    (T.target_contains_closed hsx hz)).1
  have he : (fun y ↦ carrierNullvector T Qσ col (y, z)) =ᶠ[𝓝 x]
      (fun y ↦ carrierNullvector T Q₀ col (σ • y, z)) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact current_carrierNullvector_source_dilation T Q₀ Qσ hF hrank
      hphysical hseed htrans hσ hσ1 hscaled col hy hz
  have hop := reducedOperator_eq_of_germ (sourceDilation F σ) Qσ.1 he
  have hscale := reducedOperator_sourceDilation_pullback hU hF hflat hσ hxU (hrank _ hxU) hk 1
  simp only [one_smul, one_mul] at hscale
  unfold carrierTransportPotential
  rw [current_carrierConullvector_source_dilation T Q₀ Qσ hF hrank
      hphysical hseed htrans hσ hσ1 hscaled row hx hz,
    current_carrierAdaptedDenominator_source_dilation T Q₀ Qσ hF hrank
      hphysical hseed htrans hσ hσ1 hscaled row col hx hz,
    hop, hseed, hscaled, hscale, dotProduct_smul, smul_eq_mul, mul_div_assoc]

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
