module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity.Coefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.Masks

/-!
# The literal frozen initial multiplier

At zero scale the scalar initial data enter the carrier kernel through their
square at the actual time-zero footpoint. This proves the input multiplier
identity for `app:ch_background:eq:bg-T`, preserving the phase, masks, physical
chart and initial Lebesgue measure. Its consumer is the construction of the
nonconstant frozen carrier from the SAME unit-initial extension.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel.InitialMultiplier
open ActualCarriers FrozenMenu CurrentFullPhase
open ContinuumRow CanonicalCarrier CanonicalConic

/-- The multiplier on initial Fourier data is the SQUARE of the initial
scalar at its genuine footpoint (`new:lem:scaling`, `app:ch_background:eq:bg-T`).
Consequently its contribution to the normal is the fourth power. -/
def labelWeight {n : ℕ}
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) (z : CarrierParameter) : ℝ :=
  initial (Y (0, (0, parameter z))) ^ 2

/-- The literal input multiplier is nonnegative (`app:ch_background:eq:bg-T`). -/
theorem labelWeight_nonneg {n : ℕ}
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) (z : CarrierParameter) :
    0 ≤ labelWeight Y initial z := sq_nonneg _

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)

local notation "ei" => normalizedCarrierData T Q F row col Φ Y initial hr hcell angular high 0
local notation "e₁" => normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) hr hcell angular high 0

/-- The actual zero-scale amplitude gains precisely the squared initial
scalar. No kernel or normal factorization is an input
(`new:lem:scaling`, `app:ch_background:eq:bg-T`). -/
theorem carrierAmplitude_initial (x : Torus n) (u : CarrierVariable n) :
    carrierAmplitude ei x u = labelWeight Y initial u.1 • carrierAmplitude e₁ x u := by
  simp only [carrierAmplitude, normalizedCarrierData_covector_zero,
    normalizedCarrierData_reduced_zero]
  simp only [normalizedCarrierData, data, normalizedNormal_zero]
  rw [frozenSeedNormal_initial_factor T Q F row col Φ Y initial]
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, smul_smul]
  congr 1
  dsimp only [labelWeight]
  ring

/-- Exact kernel identity on the SAME output chart with the SAME physical
phase and all original cutoffs (`app:ch_background:eq:bg-T`). -/
theorem carrierKernel_initial (x : Torus n) (u : CarrierVariable n) :
    carrierKernel ei x u = labelWeight Y initial u.1 • carrierKernel e₁ x u := by
  classical
  have hp : carrierPhase ei x u = carrierPhase e₁ x u := rfl
  have hc : (ei).outputChart = (e₁).outputChart := rfl
  by_cases hx : x ∈ (e₁).outputChart
  · simp only [carrierKernel, hc, indicator_of_mem hx, hp,
      carrierAmplitude_initial T Q F row col Φ Y initial hr hcell angular high,
      map_smul]
    exact smul_comm _ _ _
  · simp only [carrierKernel, hc, indicator_of_notMem hx, smul_zero]

/-- The literal test action is the unit kernel applied to multiplied
Euclidean initial data (`app:ch_background:eq:bg-T`). -/
theorem carrierTestIntegral_initial (f : CarrierVariable n → ℂ) (x : Torus n) :
    carrierTestIntegral ei f x =
      carrierTestIntegral e₁ (fun u ↦ (labelWeight Y initial u.1 : ℂ) * f u) x := by
  apply integral_congr_ae
  filter_upwards [] with u
  rw [carrierKernel_initial T Q F row col Φ Y initial hr hcell angular high,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, mul_comm]
  rfl

/-- Literal adjoints gain the same real label factor. The corresponding
squared adjoint norm therefore has the FOURTH power of the initial scalar
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem carrierAdjointIntegral_initial
    (w : Torus n → EuclideanSpace ℂ (Fin n)) (u : CarrierVariable n) :
    carrierAdjointIntegral ei w u =
      labelWeight Y initial u.1 • carrierAdjointIntegral e₁ w u := by
  simp only [carrierAdjointIntegral,
    carrierKernel_initial T Q F row col Φ Y initial hr hcell angular high,
    RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
    RCLike.conj_ofReal, integral_const_mul, smul_eq_mul]

/-- Outside the retained angular labels the literal kernel vanishes, at
all frequencies (`app:ch_background:defn:bg-row`). This support statement is
what permits a lower bound only on the original initial labels. -/
theorem carrierKernel_eq_zero_outside_labels
    {Z : Set CarrierParameter} (hang : ∀ z ∉ Z, ∀ θ, angular z θ = 0)
    (x : Torus n) (u : CarrierVariable n) (hu : u.1 ∉ Z) :
    carrierKernel ei x u = 0 := by
  classical
  simp [carrierKernel, carrierAmplitude, normalizedCarrierData, data, hang _ hu]

/-- The literal adjoint is supported in the original angular labels
(`app:ch_background:eq:bg-realification`). The realized adjoint inherits this
through the existing constructor's almost-everywhere integral identity. -/
theorem carrierAdjointIntegral_eq_zero_outside_labels
    {Z : Set CarrierParameter} (hang : ∀ z ∉ Z, ∀ θ, angular z θ = 0)
    (w : Torus n → EuclideanSpace ℂ (Fin n)) (u : CarrierVariable n) (hu : u.1 ∉ Z) :
    carrierAdjointIntegral ei w u = 0 := by
  simp only [carrierAdjointIntegral,
    carrierKernel_eq_zero_outside_labels T Q F row col Φ Y initial hr hcell angular high
      hang _ u hu, inner_zero_left, integral_zero]

/-- A smooth or bounded representative agreeing on the entire angular
support gives the same literal kernel, including outside that support
(`app:ch_background:eq:bg-T`). -/
theorem carrierKernel_initial_of_eqOn
    {Z : Set CarrierParameter} (hang : ∀ z ∉ Z, ∀ θ, angular z θ = 0)
    (a : CarrierParameter → ℝ) (ha : EqOn a (labelWeight Y initial) Z)
    (x : Torus n) (u : CarrierVariable n) :
    carrierKernel ei x u = a u.1 • carrierKernel e₁ x u := by
  by_cases hz : u.1 ∈ Z
  · rw [ha hz, carrierKernel_initial T Q F row col Φ Y initial hr hcell angular high]
  · rw [carrierKernel_eq_zero_outside_labels T Q F row col Φ Y initial hr hcell angular high
        hang x u hz,
      carrierKernel_eq_zero_outside_labels T Q F row col Φ Y (fun _ ↦ 1) hr hcell angular high
        hang x u hz, smul_zero]

/-- The kernel energy has the fourth initial power, with no change of
frequency normalization (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem carrierKernel_initial_norm_sq (x : Torus n) (u : CarrierVariable n) :
    ‖carrierKernel ei x u‖ ^ 2 =
      initial (Y (0, (0, parameter u.1))) ^ 4 * ‖carrierKernel e₁ x u‖ ^ 2 := by
  rw [carrierKernel_initial T Q F row col Φ Y initial hr hcell angular high,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (labelWeight_nonneg Y initial u.1), mul_pow]
  dsimp only [labelWeight]
  ring

/-- The cutoff representative gives the SAME literal test integral
(`app:ch_background:eq:bg-T`), for later identification of `V ∘ M`. -/
theorem carrierTestIntegral_initial_of_eqOn
    {Z : Set CarrierParameter} (hang : ∀ z ∉ Z, ∀ θ, angular z θ = 0)
    (a : CarrierParameter → ℝ) (ha : EqOn a (labelWeight Y initial) Z)
    (f : CarrierVariable n → ℂ) (x : Torus n) :
    carrierTestIntegral ei f x =
      carrierTestIntegral e₁ (fun u ↦ (a u.1 : ℂ) * f u) x := by
  apply integral_congr_ae
  filter_upwards [] with u
  rw [carrierKernel_initial_of_eqOn T Q F row col Φ Y initial hr hcell angular high hang a ha,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, mul_comm]
  rfl

/-- The cutoff representative gives the SAME literal adjoint integral,
including outside its agreement set (`app:ch_background:eq:bg-realification`). -/
theorem carrierAdjointIntegral_initial_of_eqOn
    {Z : Set CarrierParameter} (hang : ∀ z ∉ Z, ∀ θ, angular z θ = 0)
    (a : CarrierParameter → ℝ) (ha : EqOn a (labelWeight Y initial) Z)
    (w : Torus n → EuclideanSpace ℂ (Fin n)) (u : CarrierVariable n) :
    carrierAdjointIntegral ei w u = a u.1 • carrierAdjointIntegral e₁ w u := by
  simp only [carrierAdjointIntegral,
    carrierKernel_initial_of_eqOn T Q F row col Φ Y initial hr hcell angular high hang a ha,
    RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
    RCLike.conj_ofReal, integral_const_mul, smul_eq_mul]

/-- The SAME realized unit adjoint is supported in the original angular
labels. The input `hVadj` is exactly the already proved literal-adjoint output
of `FrozenIncidencePatchData.exists_common_measurement_realization` (also
retained by `FrozenCoercivity.exists_finite_realized_frozen_row_gap`). No
operator support or norm comparison is assumed (`app:ch_background:eq:bg-T`). -/
theorem unit_adjoint_supported
    {Z : Set CarrierParameter} (hang : ∀ z ∉ Z, ∀ θ, angular z θ = 0)
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hVadj : ∀ w : ComplexOutputL2 n,
      V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e₁ w)
    (w : ComplexOutputL2 n) :
    ∀ᵐ u ∂carrierMeasure n, u.1 ∉ Z → V.adjoint w u = 0 := by
  filter_upwards [hVadj w] with u hu
  intro hz
  rw [hu]
  exact carrierAdjointIntegral_eq_zero_outside_labels T Q F row col Φ Y (fun _ ↦ 1)
    hr hcell angular high hang w u hz

end JanetCartan.ContinuumNormal.FrozenModel.InitialMultiplier
