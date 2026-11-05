module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.Polynomial
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalAmplitude

/-!
# The background-modulation endpoint of the original continuum row

Contract the actual Hermitian polynomial with the SAME projected stress.
Its zero endpoint is the squared compatible normal times the reduced
covector. The original continuum kernel is recovered with its literal
physical, carrier, angular and high-pass cutoffs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Matrix
open scoped ContDiff Matrix.Norms.Frobenius InnerProductSpace

namespace JanetCartan.Sampling.BackgroundModulation
open RawPrimary LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.LeadingPrimitive NullTransport

/-- The original projected-stress contraction, extended complex linearly
without conjugating the input tensor. Its coefficients are the actual real
stresses of the retained frame (`app:ch_background:setup:bg-wkb-input`). -/
def complexStressContraction {n : ℕ} (S : Fin n → MetricTensor n) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ WithLp.toLp 2 (fun i ↦ ∑ j, ∑ k, (S i j k : ℂ) * A j k)
      map_add' := by intros; ext i; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intros
        ext i
        simp [Finset.mul_sum, mul_left_comm] }

/-- The exact stress contraction of the rank-one Hermitian endpoint is the
normal square times the original reduced covector; no detector is replaced
(`app:ch_background:eq:bg-T`, `app:ch_background:setup:bg-wkb-input`). -/
theorem complexStressContraction_rankOne {n N : ℕ}
    (S : Fin n → MetricTensor n) (ν : Euclidean N) (ξ : Euclidean n) :
    complexStressContraction S (fun i j ↦ ((‖ν‖ ^ 2 * ξ i * ξ j : ℝ) : ℂ)) =
      ((‖ν‖ ^ 2 : ℝ) : ℂ) • euclideanComplexInclusion (ActualCarriers.quadratic S ξ) := by
  ext i
  change (∑ j, ∑ k, (S i j k : ℂ) * ((‖ν‖ ^ 2 * ξ j * ξ k : ℝ) : ℂ)) =
    ((‖ν‖ ^ 2 : ℝ) : ℂ) * ((∑ j, ∑ k, ξ j * S i j k * ξ k : ℝ) : ℂ)
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (scalar : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- The actual canonical measured amplitude, with the SAME current stress
and original physical cutoff. The background factor depends on the carrier
and inverse frequency (`app:ch_background:setup:bg-wkb-input`). -/
def measuredBackgroundModulationPolynomial (χ : Euclidean n → ℝ)
    (τ : ℝ) (z : Euclidean 3) (x : Euclidean n) (ξ : Euclidean (n - 1)) :
    EuclideanSpace ℂ (Fin n) :=
  (χ x : ℂ) • complexStressContraction (Q.1 x)
    (backgroundModulationPolynomial T Q F row col Φ Y scalar τ z x ξ)

variable (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {V : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hcompat : ∀ q ∈ V,
      let w := (FlowAmplitude.coordinates (ActualFlow.adaptedCoordinates T.data.adapted)).symm q
      scalarAmplitude T Q F row col Φ Y scalar
          (w.1, (w.2, T.reference.spatialPatch w.2)) =
        carrierScalarAmplitude T Q F row col φ y scalar w)

include hcompat in
/-- The measured zero endpoint is the continuum row's original normal square
and projected-stress detector, with the literal physical measurement retained
(`app:ch_background:setup:bg-wkb-input`). -/
theorem measuredBackgroundModulationPolynomial_zero_eq_compatible_carrier
    (χ : Euclidean n → ℝ) {p : Euclidean n × CarrierParameter}
    (hp : FlowAmplitude.coordinates (ActualFlow.adaptedCoordinates T.data.adapted)
      (p.1, parameter p.2) ∈ V) :
    measuredBackgroundModulationPolynomial T Q F row col Φ Y scalar χ 0 (parameter p.2) p.1
        (T.reference.spatialPatch (parameter p.2)) =
      ((χ p.1 * ‖normalField T Q F row col φ y scalar p.1 p.2‖ ^ 2 : ℝ) : ℂ) •
        euclideanComplexInclusion
          (ActualCarriers.quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2))) := by
  rw [measuredBackgroundModulationPolynomial,
    backgroundModulationPolynomial_zero_eq_compatible_carrier
      T Q F row col Φ Y scalar φ y hcompat hp,
    complexStressContraction_rankOne, smul_smul, Complex.ofReal_mul]

include hcompat in
/-- Exact recovery of the original continuum carrier kernel from the actual
background-modulation endpoint, before the separately specified Fourier
scalar and smooth radial band. The original carrier/angular mask, high-pass,
measurement and torus chart are unchanged (`app:ch_background:eq:bg-T`,
`app:ch_background:setup:bg-wkb-input`). -/
theorem carrierKernel_eq_backgroundModulation_zero
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (x : Torus n) (u : CarrierVariable n)
    (hx : x ∈ (data T Q F row col φ y scalar hr hcell angular high).outputChart)
    (hp : FlowAmplitude.coordinates (ActualFlow.adaptedCoordinates T.data.adapted)
      (AmplitudeBound.centeredTorusRepresentative x, parameter u.1) ∈ V) :
    carrierKernel (data T Q F row col φ y scalar hr hcell angular high) x u =
      Complex.exp (Complex.I *
        (inner ℝ (transportPosition T Q (AmplitudeBound.centeredTorusRepresentative x, u.1))
          u.2 : ℝ)) •
        (((angular u.1 (‖u.2‖⁻¹ • u.2) * high ‖u.2‖ * Real.sqrt ‖u.2‖ : ℝ) : ℂ) •
          measuredBackgroundModulationPolynomial T Q F row col Φ Y scalar
            (FixedCutoffs.physical hr 1) 0 (parameter u.1)
            (AmplitudeBound.centeredTorusRepresentative x)
            (T.reference.spatialPatch (parameter u.1))) := by
  rw [measuredBackgroundModulationPolynomial_zero_eq_compatible_carrier
    T Q F row col Φ Y scalar φ y hcompat (FixedCutoffs.physical hr 1)
      (p := (AmplitudeBound.centeredTorusRepresentative x, u.1)) hp]
  rw [carrierKernel, Set.indicator_of_mem hx]
  congr 1
  rw [carrierAmplitude, reducedCovector_data]
  ext i
  simp only [euclideanComplexInclusion_apply, PiLp.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, data, FixedCutoffs.periodic_apply]
  ring

end JanetCartan.Sampling.BackgroundModulation
