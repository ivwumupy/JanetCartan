module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.Footpoint
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationAtomMaps
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart

/-!
# Unit-scalar transport on a supplied retained chart

The matrix used in `app:ch_mean_pairs:eq:mean-density-recursion` is linear in
the initial scalar. Here the Hamilton conservation theorem is applied to the
supplied retained chart, so the scalar is evaluated at the row's actual
transported position. No new flow or row is selected.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CurrentMean.PreparationTransportPrimitives
open ContinuumRow ContinuumAdjoint.Canonical
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
open LeadingWave

/-- Relabel the original preparation scalar into the characteristic
formula's `(y,z)` coordinates. This is the fixed inverse carrier coordinate
map, with no cutoff or change of initial function
(`app:ch_mean_pairs:prop:mean-coarse`). -/
def preparationCharacteristicInitial {n : ℕ} (r : CarrierVariable n → ℝ)
    (p : Euclidean (n - 1) × Euclidean 3) : ℝ :=
  r (TransportKernel.sliceCoordinates 2 p.2, p.1)

/-- Every original scalar, including an arbitrary positive base, is
represented exactly in characteristic coordinates. This allows the
qualitative construction below to be applied to the supplied background
without selecting another scalar (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
@[simp] theorem initialScalar_preparationCharacteristicInitial {n : ℕ}
    (r : CarrierVariable n → ℝ) :
    initialScalar (preparationCharacteristicInitial r) = r := by
  funext p
  simp only [initialScalar, preparationCharacteristicInitial,
    CanonicalCarrier.parameter_eq_sliceCoordinates_symm,
    MeasurableEquiv.apply_symm_apply]

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU}
    {Ω Kc : Set (Euclidean n × Euclidean 3)}
    {p₀ : Euclidean (n - 1) × Euclidean 3} {R M τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}

/-- The original principal transport matrix, before extension or measurement,
on the SAME retained chart (`app:ch_mean_pairs:prop:mean-coarse`). -/
def retainedTransportMatrix (c : Chart T Ω Kc p₀ R M τ row col F)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (p : Euclidean n × CarrierParameter) : Matrix (Fin N) (Fin n) ℂ :=
  (principalMatrix
    (CanonicalCarrier.normalField T c.Q F row col c.forward c.inverse initial p.1 p.2)
    (T.carrierGradient c.Q p.1 (CanonicalCarrier.parameter p.2))).map Complex.ofReal

/-- The unit initial scalar constructs the matrix factor independently of
the positive background (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
def unitTransportMatrix (c : Chart T Ω Kc p₀ R M τ row col F) :
    Euclidean n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ :=
  retainedTransportMatrix c (fun _ ↦ 1)

/-- The supplied chart's ODE, inverse and null equations identify its
footpoint with the Hamilton position of the SAME row. The geometric tube
containment is retained by the carrier-flow producer; symmetry follows from
the projected frame (`app:ch_background:prop:bg-adjoint`). -/
theorem retainedChart_footpoint_eq (c : Chart T Ω Kc p₀ R M τ row col F)
    {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    (hF : ContDiffOn ℝ ∞ F U) (hrank : HasFullNormalRankOn F U)
    {K : Set (Euclidean n)} (hKU : K ⊆ U) (hτ : 0 < τ)
    (hgeom : coordinates (adaptedCoordinates T.data.adapted) ⁻¹' c.D ⊆
      (ball 0 T.physicalRadius ∩ interior K) ×ˢ parameterInterior (3 * P.radius / 2))
    {p : Euclidean n × CarrierParameter}
    (hp : coordinates (adaptedCoordinates T.data.adapted)
      (p.1, CanonicalCarrier.parameter p.2) ∈ c.D) :
    odeInitialPoint T c.inverse (p.2, p.1) =
      (CanonicalCarrier.transportPosition T c.Q p, CanonicalCarrier.parameter p.2) := by
  apply odeInitialPoint_eq_transportPosition T c.Q row col hP hKU
    (projected_frame_symmetry T c.Q F hF hrank c.frame_eq) hτ
    c.forward c.inverse hgeom c.forward_range c.inverse_range c.initial
    c.forward_inverse c.forward_parameter c.inverse_parameter c.ode _ hp
  intro w hw
  have hΩ : w ∈ Ω := by
    have hh := c.domain_coefficients hw
    simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hh
  exact ⟨(c.null_spec w hΩ).1, (c.null_spec w hΩ).2.1,
    (c.null_spec w hΩ).2.2.2⟩

/-- Factor the actual matrix into the initial scalar at the Hamilton
footpoint and the unit-scalar matrix. This uses the characteristic formula,
not an assumed factorization (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem retainedTransportMatrix_eq_initial_smul
    (c : Chart T Ω Kc p₀ R M τ row col F)
    {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    (hF : ContDiffOn ℝ ∞ F U) (hrank : HasFullNormalRankOn F U)
    {K : Set (Euclidean n)} (hKU : K ⊆ U) (hτ : 0 < τ)
    (hgeom : coordinates (adaptedCoordinates T.data.adapted) ⁻¹' c.D ⊆
      (ball 0 T.physicalRadius ∩ interior K) ×ˢ parameterInterior (3 * P.radius / 2))
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {p : Euclidean n × CarrierParameter}
    (hp : coordinates (adaptedCoordinates T.data.adapted)
      (p.1, CanonicalCarrier.parameter p.2) ∈ c.D) :
    retainedTransportMatrix c initial p =
      initialScalar initial (p.2, CanonicalCarrier.transportPosition T c.Q p) •
        unitTransportMatrix c p := by
  have he := retainedChart_footpoint_eq c hP hF hrank hKU hτ hgeom hp
  simp only [retainedTransportMatrix, unitTransportMatrix,
    normalField_eq_initial_flow, he]
  ext i j
  simp [principalMatrix, PiLp.smul_apply, initialScalar, Matrix.smul_apply,
    Complex.real_smul]
  ring

/-- The zero-density matrix of the original canonical row is exactly its
retained principal matrix, with all row cutoffs and domains unchanged
(`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem densityTransportMatrix_retained_zero
    (c : Chart T Ω Kc p₀ R M τ row col F)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {a : ℝ} (ha : 0 < a) (hcell : 4 * a < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (x : Torus n) (z : CarrierParameter) :
    densityTransportMatrix
      (CanonicalCarrier.data T c.Q F row col c.forward c.inverse initial
        ha hcell angular high) 0 x z =
      retainedTransportMatrix c initial (AmplitudeBound.centeredTorusRepresentative x, z) := by
  simp [densityTransportMatrix, CanonicalCarrier.data, retainedTransportMatrix]

/-- Defining the base extension from the unit matrix cancels division by
the original positive base everywhere. Consequently transport estimates need
no reciprocal-base seminorm (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationLinearTransport_initial_smul
    (r : CarrierVariable n → ℝ) (hr : ∀ p, 0 < r p)
    (Y : Torus n × CarrierParameter → Euclidean (n - 1))
    (A : Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (u : CarrierVariable n → ℝ) :
    preparationLinearTransport r Y (fun p ↦ r (p.2, Y p) • A p) u =
      fun p ↦ u (p.2, Y p) • A p := by
  funext p
  change (u (p.2, Y p) / r (p.2, Y p)) • (r (p.2, Y p) • A p) = _
  rw [smul_smul, div_mul_cancel₀ _ (hr _).ne']

end JanetCartan.CurrentMean.PreparationTransportPrimitives
