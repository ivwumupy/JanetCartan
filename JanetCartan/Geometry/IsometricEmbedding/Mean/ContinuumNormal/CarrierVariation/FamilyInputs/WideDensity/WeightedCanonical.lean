module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.WeightedPrimitive

/-!
# Ambient jets of the actual wider-density canonical carrier

The algebraic factorization is valid on a neighborhood of each comparison
point. Consequently it identifies every ambient derivative even when the
fixed compact density domain does not contain a neighborhood of the footpoint.
Both labels are the actual scalar-ODE inverse labels. This connects the
original wider class to `WeightedPrimitive`, without replacing the prescribed
initial scalar (in particular the source scalar `σ`) by one.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open ContinuumRow CanonicalCarrier PositiveReference
open ContinuumNormalReduction.TransportSymbol

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (initial v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))

/-- The prescribed initial scalar times `sqrt (1 + v)` gives exactly the two
ODE factors multiplying the full canonical matrix density, on a neighborhood
of each point. Positivity only at the two retained footpoints suffices; no
smallness of the density and no amplitude-continuity assumption is used.
Sources: `app:ch_background:eq:bg-Nsigma`,
`app:ch_background:eq:bg-full-complex-amplitude`, `app:ch_background:prop:bg-frame`. -/
theorem canonical_substitutedDensity_initial_mul_sqrtDensity_eventuallyEq
    (p : Variables n × Euclidean 2)
    (hg : ∀ b, ContinuousAt
      (fun q ↦ densityFootpoint T Y (densityEndpoint b (inverseCoordinates u q))) p)
    (hv : ∀ b, ContinuousAt v (densityFootpoint T Y (densityEndpoint b (inverseCoordinates u p))))
    (hpos : ∀ b, 0 < 1 + v (densityFootpoint T Y (densityEndpoint b (inverseCoordinates u p)))) :
    let a := fun initial ↦ TransportKernel.coefficientsOfCarrier
      (data T Q F row col Φ Y initial hr hcell angular high) (FixedCutoffs.physical hr 1)
    (fun q ↦ inputDensity (a (fun y ↦ initial y * Real.sqrt (1 + v y))) J
      (inverseCoordinates u q)) =ᶠ[𝓝 p]
    (fun q ↦ canonicalDensityPair T v Y (inverseCoordinates u q) •
      inputDensity (a initial) J (inverseCoordinates u q)) := by
  have hpositive (b : Bool) : ∀ᶠ q in 𝓝 p,
      0 < 1 + v (densityFootpoint T Y (densityEndpoint b (inverseCoordinates u q))) :=
    (show ContinuousAt (fun q ↦ 1 + v
        (densityFootpoint T Y (densityEndpoint b (inverseCoordinates u q)))) p from
      continuousAt_const.add ((hv b).comp
        (f := fun q ↦ densityFootpoint T Y (densityEndpoint b (inverseCoordinates u q)))
        (hg b))).eventually (eventually_gt_nhds (hpos b))
  filter_upwards [hpositive false, hpositive true] with q hl hr'
  apply canonical_inputDensity_initial_mul_sqrtDensity T Q F row col Φ Y hr hcell
    angular high initial v J (inverseCoordinates u q)
  intro b
  cases b
  · exact hl.le
  · exact hr'.le

/-- Equality of finite ambient norms for the ACTUAL wider-density carrier
and its full two-footpoint factorization after the genuine conic inverse.
`b₀` may be the normalized zero slice or a second positive reference. The
original density interval supplies strict positivity; smoothness is needed
only at points of the fixed density domain. Consumer: the actual-family
instantiation of `exists_weighted_inputDensity_inverse_sub_le_of_primitive_norms`.
Sources: `app:ch_background:prop:bg-normalized`,
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem canonical_substitutedDensity_initial_mul_sqrtDensity_cNorm_sub
    {K : Set (Variables n × Euclidean 2)}
    {L : Set (Euclidean (n - 1) × Euclidean 3)}
    (hg : ∀ b p, p ∈ K → ContinuousAt
      (fun q ↦ densityFootpoint T Y (densityEndpoint b (inverseCoordinates u q))) p)
    (hrange : ∀ b p, p ∈ K → densityFootpoint T Y (densityEndpoint b (inverseCoordinates u p)) ∈ L)
    (hv : ∀ y ∈ L, ContDiffAt ℝ ∞ v y)
    (hpos : ∀ y ∈ L, (1 / 2 : ℝ) ≤ 1 + v y)
    (b₀ : Variables n × Euclidean 2 → Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    let a := fun initial ↦ TransportKernel.coefficientsOfCarrier
      (data T Q F row col Φ Y initial hr hcell angular high) (FixedCutoffs.physical hr 1)
    cNorm K m ((fun q ↦ inputDensity (a (fun y ↦ initial y * Real.sqrt (1 + v y))) J
      (inverseCoordinates u q)) - b₀) =
    cNorm K m ((fun q ↦ canonicalDensityPair T v Y (inverseCoordinates u q) •
      inputDensity (a initial) J (inverseCoordinates u q)) - b₀) := by
  apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
  intro p hp
  have he := canonical_substitutedDensity_initial_mul_sqrtDensity_eventuallyEq
    T Q F row col Φ Y hr hcell angular high initial v J u p
    (fun b ↦ hg b p hp) (fun b ↦ (hv _ (hrange b p hp)).continuousAt)
    (fun b ↦ lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hpos _ (hrange b p hp)))
  exact he.sub (Filter.EventuallyEq.refl _ _)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
