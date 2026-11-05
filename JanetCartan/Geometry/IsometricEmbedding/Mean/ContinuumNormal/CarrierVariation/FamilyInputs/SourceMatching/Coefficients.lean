module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.Transport
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.NormalizedCoefficients

/-!
# The retained covector, adjugate column, and reduced detector

These are the coefficient identities in `app:ch_background:eq:bg-Nsigma`
which follow from Hamilton matching without identifying the scalar transport.
They use the same selected adjugate column at both scales. The scalar amplitude
and hence the actual principal normal still require their own ODE comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
open HamiltonPhase NormalizedBackground.SourceGeometry
open ActualCarriers CurrentFullPhase ContinuumRow NullTransport

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

/-- The physical carrier covector is the unweighted seed pullback. The phase
identity is differentiated on an open physical ball, rather than only on a
closed carrier support. Source: `app:ch_background:eq:bg-Nsigma`.
Consumer: the actual null column and reduced coefficient below. -/
theorem current_carrierGradient_source_dilation {x : Euclidean n}
    (hx : x ∈ ball 0 T.physicalRadius) {z : Euclidean 3}
    (hz : z ∈ FrozenMenu.parameterCube (2 * P.radius)) :
    T.carrierGradient Qσ x z = T.carrierGradient Q₀ (σ • x) z := by
  have hphase := (projected_current_chart_source_dilation T Q₀ Qσ hF hrank
    hphysical hseed htrans hσ hσ1 hscaled).2.1
  have hsx : σ • x ∈ ball 0 T.physicalRadius := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
    exact (mul_le_of_le_one_left (norm_nonneg x) hσ1).trans_lt (mem_ball_zero_iff.mp hx)
  have hdiff : DifferentiableAt ℝ (fun y ↦ T.carrier Q₀ y z) (σ • x) :=
    (hasGradientAt_carrierPhase (T.currentChart Q₀) T.reference.spatialPatch
      (T.target_contains_closed hsx hz)).differentiableAt
  have heq : (fun y ↦ T.carrier Qσ y z) =ᶠ[𝓝 x]
      (fun y ↦ sourcePhase (fun p : Euclidean n × Euclidean 3 ↦ T.carrier Q₀ p.1 p.2)
        σ (y, z)) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact hphase (T.target_contains_closed hy hz)
  exact heq.gradient_eq.trans (gradient_sourcePhase_position hσ.ne' hdiff)

/-- The identical selected adjugate column pulls back with the physical
covector. There is no rescaling or re-selection of its index.
Source: `app:ch_background:eq:bg-Nsigma`. Consumer: scalar/null matching. -/
theorem current_carrierNullvector_source_dilation (col : Fin n) {x : Euclidean n}
    (hx : x ∈ ball 0 T.physicalRadius) {z : Euclidean 3}
    (hz : z ∈ FrozenMenu.parameterCube (2 * P.radius)) :
    carrierNullvector T Qσ col (x, z) = carrierNullvector T Q₀ col (σ • x, z) := by
  have hsx := (convex_ball (0 : Euclidean n) T.physicalRadius).smul_mem_of_zero_mem
    (mem_ball_self T.physicalRadius_pos) hx ⟨hσ.le, hσ1⟩
  have hxU : σ • x ∈ U :=
    (carrierPhase_gradient_mem_domain (T.currentChart Q₀) T.reference.spatialPatch
      (T.target_contains_closed hsx hz)).1
  have hgrad := current_carrierGradient_source_dilation T Q₀ Qσ hF hrank
    hphysical hseed htrans hσ hσ1 hscaled hx hz
  have hframe : Qσ.1 x = Q₀.1 (σ • x) := by
    rw [hseed, hscaled]
    exact funext (ProjectedStressFrame.projectedStress_sourceDilation hσ hF x (hrank _ hxU))
  simp only [carrierNullvector, hgrad, hframe]

/-- The normalized source coefficient is the actual retained reduced detector
on the fixed patch. The arbitrary `b` is unused by the reduced coefficient;
this theorem makes no assertion about the normal coefficient or scalar ODE.
Source: `app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-frame`.
Consumer: primitive coefficient comparison in `FamilyInputs`. -/
theorem normalizedSourceCoefficients_reduced_eq_current
    (b : Euclidean n × (ℝ × Euclidean 2) → Euclidean n)
    (measurement : Euclidean n → ℝ)
    (angular : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {p : Euclidean n × (ℝ × Euclidean 2)}
    (hx : p.1 ∈ ball 0 T.physicalRadius)
    (hz : CanonicalCarrier.parameter p.2 ∈ FrozenMenu.parameterCube (2 * P.radius)) :
    (normalizedSourceCoefficients F
      (fun q ↦ T.carrierGradient Q₀ q.1 (CanonicalCarrier.parameter q.2))
      b measurement angular high σ).reduced p =
      (quadratic (Qσ.1 p.1) (T.carrierGradient Qσ p.1 (CanonicalCarrier.parameter p.2))).ofLp := by
  have hsx := (convex_ball (0 : Euclidean n) T.physicalRadius).smul_mem_of_zero_mem
    (mem_ball_self T.physicalRadius_pos) hx ⟨hσ.le, hσ1⟩
  have hxU : σ • p.1 ∈ U :=
    (carrierPhase_gradient_mem_domain (T.currentChart Q₀) T.reference.spatialPatch
      (T.target_contains_closed hsx hz)).1
  have hgrad := current_carrierGradient_source_dilation T Q₀ Qσ hF hrank
    hphysical hseed htrans hσ hσ1 hscaled hx hz
  have hframe : Qσ.1 p.1 = ProjectedStressFrame.projectedStress F (σ • p.1) := by
    rw [hscaled]
    exact funext (ProjectedStressFrame.projectedStress_sourceDilation hσ hF p.1 (hrank _ hxU))
  simp only [normalizedSourceCoefficients, hgrad, hframe]

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
