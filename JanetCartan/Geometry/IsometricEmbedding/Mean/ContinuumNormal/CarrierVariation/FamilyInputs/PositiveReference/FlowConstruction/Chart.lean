module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.CoefficientDependence
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence

/-!
# Retained positive null-flow witnesses

The data in this file are produced by `FlowConstruction.Construction` from the
actual coefficient and ODE constructors. There is no continuity estimate among
these fields. The comparison theorem below applies the proved coefficient/ODE
implication to the retained maps, including their literal scalar and footpoint.
Consumer: `PositiveReference`, for `app:ch_background:prop:bg-frame` and
`app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow ProjectedStressFrame

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The actual coefficients and retained ODE witnesses of
`app:ch_waves:thm:leading`. The constructor proves every field from primitive
immersion hypotheses; no flow or scalar dependence is stored as a field. -/
structure Chart (Ω K : Set (Euclidean n × Euclidean 3))
    (p₀ : Euclidean (n - 1) × Euclidean 3) (R M τ : ℝ) (row col : Fin n)
    (F : Euclidean n → Euclidean N) where
  Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold}
  frame_eq : Q.1 = projectedStress F
  null_smooth : ContDiffOn ℝ ∞ (carrierNullvector T Q col) Ω
  conull_smooth : ContDiffOn ℝ ∞ (carrierConullvector T Q row) Ω
  direction_smooth : ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ω
  potential_smooth : ContDiffOn ℝ ∞ (carrierTransportPotential T Q F row col) Ω
  direction_bound : cNorm K 1 (carrierTransportDirection T Q row col) ≤ M
  symm : ∀ w ∈ Ω, ∀ i, (Q.1 w.1 i).IsSymm
  null_spec : ∀ w ∈ Ω,
    carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
    reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
      (fun j ↦ carrierNullvector T Q col w j) = 0 ∧
    carrierConullvector T Q row w ᵥ*
      reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
    carrierAdaptedDenominator T Q row col w ≠ 0
  D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))
  forward : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3
  inverse : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3
  domain_eq : D = (fun q ↦ (q.1, forward q)) '' (Ioo (-τ) τ ×ˢ ball p₀ (R / 8))
  domain_open : IsOpen D
  small_subset : Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D
  subset_big : D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4)
  domain_coefficients : D ⊆
    (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm ⁻¹' Ω
  forward_smooth : ContDiffOn ℝ ∞ forward (Ioo (-τ) τ ×ˢ ball p₀ (R / 8))
  inverse_smooth : ContDiffOn ℝ ∞ inverse D
  forward_range : MapsTo (fun q ↦ (q.1, forward q)) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) D
  inverse_range : MapsTo (fun q ↦ (q.1, inverse q)) D (Ioo (-τ) τ ×ˢ ball p₀ (R / 8))
  initial : ∀ p ∈ ball p₀ (R / 8), forward (0, p) = p
  inverse_forward : ∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ,
    inverse (t, forward (t, p)) = p
  forward_inverse : ∀ q ∈ D, forward (q.1, inverse q) = q.2
  forward_parameter : ∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ, (forward (t, p)).2 = p.2
  inverse_parameter : ∀ q ∈ D, (inverse q).2 = q.2.2
  ode : ∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ,
    HasDerivAt (fun s ↦ forward (s, p))
      ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q row col
        ((FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
          (t, forward (t, p))))).2, 0) t
  forward_buffer_smooth : ContDiffOn ℝ ∞ forward
    (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4))
  inverse_buffer_smooth : ContDiffOn ℝ ∞ inverse
    (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4))

variable {T} {Ω K : Set (Euclidean n × Euclidean 3)}
    {p₀ : Euclidean (n - 1) × Euclidean 3} {R M τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}

/-- The literal scalar of the SAME retained flow, for
`app:ch_waves:thm:leading`; this is a definition, not a separately chosen
transport solution. -/
def Chart.scalar (c : Chart T Ω K p₀ R M τ row col F)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) : Euclidean n × Euclidean 3 → ℝ :=
  carrierScalarAmplitude T c.Q F row col c.forward c.inverse initial

/-- The actual characteristic formula satisfies the prescribed positive
problem, including the scalar PDE and the reduced null equation
(`app:ch_waves:thm:leading`). -/
theorem Chart.scalar_spec (c : Chart T Ω K p₀ R M τ row col F) (hτ : 0 < τ)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ContDiffOn ℝ ∞ initial (ball p₀ (R / 8)))
    (hipos : ∀ p ∈ ball p₀ (R / 8), 0 < initial p) :
    let C := FlowAmplitude.coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
    let α := c.scalar initial
    ContDiffOn ℝ ∞ α (C ⁻¹' c.D) ∧
    ContDiffOn ℝ ∞ (fun w ↦ α w • carrierNullvector T c.Q col w) (C ⁻¹' c.D) ∧
    (∀ p ∈ ball p₀ (R / 8), α (T.data.adapted.embedding p.1, p.2) = initial p) ∧
    (∀ w ∈ C ⁻¹' c.D, 0 < α w) ∧
    (∀ L : Set (Euclidean n × Euclidean 3), IsCompact L → L ⊆ C ⁻¹' c.D →
      ∃ a > 0, ∀ w ∈ L, a ≤ α w) ∧
    (∀ w ∈ C ⁻¹' c.D,
      fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T c.Q row col w) +
        carrierTransportPotential T c.Q F row col w * α w = 0) ∧
    (∀ w ∈ C ⁻¹' c.D, reducedSymbol (c.Q.1 w.1) (T.carrierGradient c.Q w.1 w.2) *ᵥ
      (fun j ↦ (α w • carrierNullvector T c.Q col w) j) = 0) ∧
    (∀ w ∈ C ⁻¹' c.D, carrierConullvector T c.Q row w ⬝ᵥ reducedOperator F c.Q.1
      (fun x ↦ α (x, w.2) • carrierNullvector T c.Q col (x, w.2)) w.1 = 0) := by
  let C := FlowAmplitude.coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  have hphys : C ⁻¹' c.D ⊆ Ω := by
    intro w hw
    have hh := c.domain_coefficients hw
    change C.symm (C w) ∈ Ω at hh
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
  exact carrierScalarAmplitude_spec T c.Q F row col isOpen_Ioo ordConnected_Ioo
    isOpen_ball c.domain_open ⟨neg_neg_of_pos hτ, hτ⟩
    (c.null_smooth.mono hphys) (c.potential_smooth.mono hphys)
    (fun w hw ↦ c.symm w (hphys hw))
    (fun w hw ↦ (c.null_spec w (hphys hw)).2.2.2.2)
    (fun w hw ↦ (c.null_spec w (hphys hw)).2.2.1)
    hi hipos c.forward_smooth c.forward_range c.initial c.inverse_smooth
    c.inverse_range c.inverse_forward c.forward_inverse c.ode

/-- The literal density footpoint of the constructed inverse has a fixed
compact range, independently of the initial scalar
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem Chart.densityFootpoint_spec (c : Chart T Ω K p₀ R M τ row col F) :
    let W := densityCoordinates T ⁻¹' (Ioo (-τ) τ ×ˢ ball p₀ (R / 32))
    IsCompact (closedBall p₀ (R / 8)) ∧
    ContDiffOn ℝ ∞ (densityFootpoint T c.inverse) W ∧
    MapsTo (densityFootpoint T c.inverse) W (closedBall p₀ (R / 8)) ∧
    (∀ w ∈ W, (densityFootpoint T c.inverse w).2 = ContinuumRow.CanonicalCarrier.parameter w.2) :=
  ⟨isCompact_closedBall _ _,
    c.inverse_smooth.comp (densityCoordinates T).contDiff.contDiffOn (fun _ hw ↦ c.small_subset hw),
    densityFootpoint_mapsTo_closedBall T (fun _ hw ↦ c.small_subset hw) c.inverse_range,
    fun _ hw ↦ c.inverse_parameter _ (c.small_subset hw)⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
