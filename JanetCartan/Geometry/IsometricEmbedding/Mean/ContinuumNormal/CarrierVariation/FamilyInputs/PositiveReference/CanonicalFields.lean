module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NormalDependence
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.CanonicalDensity

/-!
# Literal coefficients of the retained positive flow

These are the fields consumed by the fixed-positive-reference assembly for
`app:ch_background:prop:bg-frame` and `app:ch_osc:prop:osc-normal`, Step 4'.
The definitions retain the same Hamilton family, adjugate column and ODE maps.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow
open ContinuumRow CanonicalCarrier ContinuumNormalReduction.TransportSymbol

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU} {Ω K : Set (Euclidean n × Euclidean 3)}
    {p₀ : Euclidean (n - 1) × Euclidean 3} {R M τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}

/-- The SAME canonical normal in joint physical/carrier variables, as in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
def Chart.normal (c : Chart T Ω K p₀ R M τ row col F)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) :
    Euclidean n × CarrierParameter → Euclidean N :=
  Function.uncurry (normalField T c.Q F row col c.forward c.inverse initial)

/-- The literal reduced detector, in the finite-product coefficient norm of
`app:ch_background:eq:bg-full-complex-amplitude`. -/
def Chart.reduced (c : Chart T Ω K p₀ R M τ row col F) :
    Euclidean n × CarrierParameter → Fin n → ℝ :=
  fun p ↦ (quadratic (c.Q.1 p.1) (T.carrierGradient c.Q p.1 (parameter p.2))).ofLp

/-- Identification with the actual coefficient fields, including every fixed
mask, for `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem Chart.coefficients_eq (c : Chart T Ω K p₀ R M τ row col F)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ) :
    TransportKernel.coefficientsOfCarrier
      (data T c.Q F row col c.forward c.inverse initial hr hcell angular high)
      (FixedCutoffs.physical hr 1) =
      ({ measurement := FixedCutoffs.physical hr 1
         angular := fun p ↦ angular p.1 p.2
         high := high
         normal := c.normal initial
         reduced := c.reduced } : Coefficients n N) :=
  coefficientsOfCarrier_data T c.Q F row col c.forward c.inverse initial hr hcell angular high

/-- The constructed scalar is smooth at every point of a fixed carrier
compact mapped into the common output cylinder. Its producer is the actual
scalar PDE theorem, not an assumed family regularity statement
(`app:ch_waves:thm:leading`). -/
theorem Chart.scalar_contDiffAt (c : Chart T Ω K p₀ R M τ row col F)
    (hR : 0 < R) (hτ : 0 < τ)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ContDiffOn ℝ ∞ initial (ball p₀ (R / 8)))
    (hipos : ∀ p ∈ ball p₀ (R / 8), 0 < initial p)
    {L : Set (Euclidean n × CarrierParameter)}
    (hL : MapsTo (densityCoordinates T) L (outputCylinder p₀ R τ)) :
    ∀ p ∈ L, ContDiffAt ℝ ∞
      (fun p : Euclidean n × CarrierParameter ↦ c.scalar initial (p.1, parameter p.2)) p := by
  let C := FlowAmplitude.coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  have hopen : IsOpen (C ⁻¹' c.D) := c.domain_open.preimage C.continuous
  intro p hp
  have hmem : (p.1, parameter p.2) ∈ C ⁻¹' c.D :=
    c.small_subset ((outputCylinder_spec hR hτ).2 (hL hp))
  exact ((c.scalar_spec hτ initial hi hipos).1.contDiffAt (hopen.mem_nhds hmem)).comp p
    (contDiffAt_fst.prodMk (parameter.contDiff.contDiffAt.comp p contDiffAt_snd))

/-- Both literal density factors are evaluated at this ODE footpoint in one
fixed compact range. This is independent of the initial scalar and the varying
immersion (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem Chart.densityFootpoint_range (c : Chart T Ω K p₀ R M τ row col F)
    (hR : 0 < R) (hτ : 0 < τ)
    {L : Set (Euclidean n × CarrierParameter)}
    (hL : MapsTo (densityCoordinates T) L (outputCylinder p₀ R τ)) :
    MapsTo (densityFootpoint T c.inverse) L (closedBall p₀ (R / 8)) :=
  fun _ hp ↦ c.densityFootpoint_spec.2.2.1 ((outputCylinder_spec hR hτ).2 (hL hp))

/-- The initial scalar occurs at both actual ODE footpoints in the full
normal density. This instantiates `canonical_inputDensity_initial` for the
retained charts (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem Chart.inputDensity_initial (c : Chart T Ω K p₀ R M τ row col F)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (J : InputVariables n → ℝ) (p : InputVariables n) :
    let coeff := fun initial ↦ TransportKernel.coefficientsOfCarrier
      (data T c.Q F row col c.forward c.inverse initial hr hcell angular high)
      (FixedCutoffs.physical hr 1)
    inputDensity (coeff initial) J p =
      (initial (densityFootpoint T c.inverse (p.1.1, p.2.1)) ^ 2 *
        initial (densityFootpoint T c.inverse (p.1.2, p.2.1)) ^ 2) •
        inputDensity (coeff (fun _ ↦ 1)) J p :=
  canonical_inputDensity_initial T c.Q F row col c.forward c.inverse hr hcell angular high
    initial J p

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
