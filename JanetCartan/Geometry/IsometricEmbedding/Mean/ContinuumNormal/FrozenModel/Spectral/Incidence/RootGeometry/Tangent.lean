module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.CanonicalData

/-!
# The actual seed differential parametrizes the characteristic tangent space

The Hamilton initial section gives both the tangential projection identity and
the characteristic equation. Their derivatives solve the frequency equation
in `app:ch_background:prop:bg-frame`, for the same quantitative family. The
consumer is the root placement required by `exists_canonicalFrozen_weight_threshold`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts HamiltonPhase ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The actual seed momentum retains its prescribed tangential component and
zero energy, by the Hamilton initial-section identities
(`app:lem:common-hamilton-phase`, `app:ch_background:prop:bg-frame`). -/
theorem seedCovector_initial_identities {ζ : Euclidean (n - 1)}
    (hs : (0, (0, (0, ζ))) ∈ (T.currentChart Q).source) :
    T.data.adapted.embedding.toContinuousLinearMap.adjoint (seedCovector T Q ζ) = ζ ∧
    determinant (Q.1 0) (seedCovector T Q ζ) = 0 := by
  have ha := (T.currentChart Q).source_admissible _ hs
  have hx : (T.family.flow Q).position (0, (0, (0, ζ))) = 0 := by
    rw [(T.family.flow Q).initial_position _ ha.2, T.family.section_eq, map_zero]
  have ht := (T.currentChart Q).maps_to_target _ hs
  rw [hx] at ht
  have hc := (T.currentChart Q).left_inverse _ hs
  rw [hx] at hc
  have he : seedCovector T Q ζ = (T.family.flow Q).momentum (0, (0, (0, ζ))) := by
    change gradient (fun x ↦ phase (T.currentChart Q).coordinates (x, (0, ζ))) 0 = _
    rw [(T.currentChart Q).gradient_phase_eq_chartMomentum ht]
    simp only [ProjectionChart.chartMomentum, chartLift, hc]
  rw [he]
  constructor
  · apply ext_inner_right ℝ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left, ← T.family.section_eq Q]
    exact (T.family.flow Q).initial_momentum _ ha.2 v
  · have henergy := (T.family.flow Q).initial_energy _ ha.2
    rw [hx] at henergy
    have hm := (T.family.flow Q).state_mem _ ha.1 _ ha.2
    exact (normalizedSymbol_eq_zero_iff Q.1 (z := (0, _)) hm.2).mp henergy

/-- Differentiating the actual initial-section identities gives a right inverse
of tangential projection whose image is characteristic tangent
(`app:ch_background:prop:bg-frame`, tangent-hyperplane argument). -/
theorem seedCovector_differential_identities {ζ : Euclidean (n - 1)}
    (hs : (0, (0, (0, ζ))) ∈ (T.currentChart Q).source)
    (hζ : ζ ∈ ball (ActualPhase.covectorCenter T) T.family.radius)
    (η : Euclidean (n - 1)) :
    T.data.adapted.embedding.toContinuousLinearMap.adjoint
      (fderiv ℝ (seedCovector T Q) ζ η) = η ∧
    fderiv ℝ (determinant (Q.1 0)) (seedCovector T Q ζ)
      (fderiv ℝ (seedCovector T Q) ζ η) = 0 := by
  have hd := ((seedCovector_smooth T Q).contDiffAt
    (isOpen_ball.mem_nhds hζ)).differentiableAt (by simp)
  have hsrc : ∀ᶠ w in 𝓝 ζ, (0, (0, (0, w))) ∈ (T.currentChart Q).source :=
    (show ContinuousAt (fun w : Euclidean (n - 1) ↦
      ((0 : ℝ), ((0 : Euclidean (n - 1)), ((0 : ℝ), w)))) ζ by fun_prop)
      ((T.currentChart Q).isOpen_source.mem_nhds hs)
  constructor
  · have he : (fun w ↦ T.data.adapted.embedding.toContinuousLinearMap.adjoint
        (seedCovector T Q w)) =ᶠ[𝓝 ζ] id := by
      filter_upwards [hsrc] with w hw
      exact (seedCovector_initial_identities T Q hw).1
    have hh := (T.data.adapted.embedding.toContinuousLinearMap.adjoint.hasFDerivAt.comp ζ
      hd.hasFDerivAt).unique ((hasFDerivAt_id ζ).congr_of_eventuallyEq he)
    exact congrArg (fun L : Euclidean (n - 1) →L[ℝ] Euclidean (n - 1) ↦ L η) hh
  · have hp : DifferentiableAt ℝ (determinant (Q.1 0)) (seedCovector T Q ζ) :=
      (contDiff_determinant.comp (contDiff_const.prodMk contDiff_id)).differentiable
        (by simp) |>.differentiableAt
    have he : (fun w ↦ determinant (Q.1 0) (seedCovector T Q w)) =ᶠ[𝓝 ζ]
        (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [hsrc] with w hw
      exact (seedCovector_initial_identities T Q hw).2
    have hh := (hp.hasFDerivAt.comp ζ hd.hasFDerivAt).unique
      ((hasFDerivAt_const (0 : ℝ) ζ).congr_of_eventuallyEq he)
    exact congrArg (fun L : Euclidean (n - 1) →L[ℝ] ℝ ↦ L η) hh

/-- Every characteristic tangent covector is recovered by the derivative of
the SAME actual seed map applied to its adapted tangential projection
(`app:ch_background:prop:bg-frame`). The pivot is the original adapted normal
derivative: `NullTransport.exists_actual_null_gaps` produces a positive lower
bound at physical zero on this exact three-halves parameter cube, from primitive
frame closeness. No surjectivity or frequency equation is assumed. -/
theorem seedCovector_differential_adjoint_of_tangent
    {c C : ℝ} (hP : P.IsValid c C) {z : Euclidean 3}
    (hz : z ∈ parameterCube (3 * P.radius / 2))
    (hpivot : fderiv ℝ (determinant (Q.1 0)) (T.carrierGradient Q 0 z)
      T.data.adapted.normal ≠ 0)
    {k : Euclidean n}
    (hk : fderiv ℝ (determinant (Q.1 0)) (T.carrierGradient Q 0 z) k = 0) :
    fderiv ℝ (seedCovector T Q) (T.reference.spatialPatch z)
      (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) = k := by
  let A := T.data.adapted.embedding.toContinuousLinearMap.adjoint
  let B := fderiv ℝ (seedCovector T Q) (T.reference.spatialPatch z)
  let d := fderiv ℝ (determinant (Q.1 0)) (T.carrierGradient Q 0 z)
  have hz₂ : z ∈ parameterCube (2 * P.radius) :=
    fun i ↦ (hz i).trans (by linarith [hP.1])
  have hs := T.current_section_source Q
    (u := 0) (by simpa using T.reference.radius_pos) hz₂
  have hbuf : T.reference.spatialPatch z ∈
      ball (ActualPhase.covectorCenter T) T.family.radius := by
    simpa only [parameter_apply, carrierParameters_spectatorCenter] using
      spatialPatch_mem_phaseBuffer T hP (z := (z 0, spectatorCenter z))
        (by simpa only [parameter_apply, carrierParameters_spectatorCenter] using hz)
  have hb := seedCovector_differential_identities T Q hs hbuf (A k)
  have hb' : A (B (A k)) = A k ∧ d (B (A k)) = 0 := by
    exact hb
  let w := k - B (A k)
  have hwA : A w = 0 := by simp only [w, map_sub, hb'.1, sub_self]
  have hwd : d w = 0 := by simp only [w, map_sub, hb'.2, hk, sub_self, d]
  have hw := T.data.adapted.covector_decomposition w
  change ⟪T.data.adapted.normal, w⟫_ℝ • T.data.adapted.normal +
    T.data.adapted.embedding (A w) = w at hw
  rw [hwA, map_zero, add_zero] at hw
  have hdw := congrArg d hw
  rw [map_smul, hwd] at hdw
  have hcoeff : ⟪T.data.adapted.normal, w⟫_ℝ = 0 :=
    (mul_eq_zero.mp hdw).resolve_right hpivot
  rw [hcoeff, zero_smul] at hw
  exact (sub_eq_zero.mp hw.symm).symm
end JanetCartan.ContinuumNormal.FrozenModel
