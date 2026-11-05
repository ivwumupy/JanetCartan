module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Regularization

/-!
# Compact parameter masks and the original radial kernel

`MaskHypotheses` requires compact support of the mask itself, whereas
`TransportKernel.SymbolInputs` describes a purely radial mask. For the actual
carrier in `app:ch_background:eq:bg-T`, the angular coefficient already has
compact parameter support. Truncating a radial mask to that support leaves the
kernel, operator action and adjoint unchanged. This supplies compatible inputs
to the finite global normal identification without changing either interface.
-/

@[expose] public noncomputable section
open MeasureTheory Set
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open TransportKernel
variable {n N : ℕ}

/-- Compact parameter truncation used only to construct the finite operator;
the symbol keeps the original radial mask (`app:ch_background:eq:bg-T`). -/
def parameterTruncatedMask (Z : Set CarrierParameter) (m : CarrierVariable n → ℝ) :
    CarrierVariable n → ℝ := (Prod.fst ⁻¹' Z).indicator m

/-- Construct the existing finite-mask hypotheses from compact parameter
support, a bounded finite-frequency mask, and the primitive kernel hypotheses.
The radial mask need not vanish in the parameter direction
(`app:ch_background:eq:bg-T`). -/
theorem maskHypotheses_parameterTruncatedMask
    (d : CarrierData n N) (Z : Set CarrierParameter) (m : CarrierVariable n → ℝ)
    {R M C : ℝ} (hcompact : IsCompact Z) (hR : 0 ≤ R) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hk : StronglyMeasurable (Function.uncurry (carrierKernel d)))
    (hm : StronglyMeasurable m)
    (hfreq : ∀ u, R < ‖u.2‖ → m u = 0) (hbound : ∀ u, |m u| ≤ M)
    (ha : ∀ x u, ‖carrierAmplitude d x u‖ ≤ C * Real.sqrt ‖u.2‖) :
    CarrierRegularization.MaskHypotheses d (parameterTruncatedMask Z m) Z R M C where
  compact_parameters := hcompact
  radius_nonneg := hR
  mask_bound_nonneg := hM
  amplitude_bound_nonneg := hC
  kernel_measurable := hk
  mask_measurable := hm.indicator (hcompact.measurableSet.preimage measurable_fst)
  mask_support := by
    intro u hu
    by_cases hz : u.1 ∈ Z
    · have hr : R < ‖u.2‖ := by
        have hn : u.2 ∉ Metric.closedBall 0 R := fun hball ↦ hu ⟨hz, hball⟩
        simpa using hn
      simp [parameterTruncatedMask, hz, hfreq u hr]
    · simp [parameterTruncatedMask, hz]
  mask_bound := by
    intro u
    by_cases hz : u.1 ∈ Z
    · simpa [parameterTruncatedMask, hz] using hbound u
    · simpa [parameterTruncatedMask, hz] using hM
  amplitude_bound := ha

variable (d : CarrierData n N) {Z : Set CarrierParameter}
    (hZ : ∀ z ∉ Z, ∀ η, d.angularCutoff z η = 0)

include hZ

/-- The angular support gives literal kernel vanishing outside the parameter
set (`app:ch_background:eq:bg-T`). -/
theorem carrierKernel_eq_zero_outside_parameters (x : Torus n)
    (u : CarrierVariable n) (hu : u.1 ∉ Z) : carrierKernel d x u = 0 := by
  classical
  by_cases hx : x ∈ d.outputChart <;>
    simp [carrierKernel, carrierAmplitude, hx, hZ u.1 hu]

/-- Parameter truncation does not alter the masked kernel at any point
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem maskedCarrierKernel_parameterTruncatedMask (m : CarrierVariable n → ℝ) :
    maskedCarrierKernel d (parameterTruncatedMask Z m) = maskedCarrierKernel d m := by
  funext x u
  by_cases hu : u.1 ∈ Z
  · simp [maskedCarrierKernel, parameterTruncatedMask, hu]
  · simp [maskedCarrierKernel, carrierKernel_eq_zero_outside_parameters d hZ x u hu]

/-- Both finite source integrals are literally equal, including on arbitrary
representatives (`app:ch_background:eq:bg-T`). -/
theorem regularizedCarrierIntegral_parameterTruncatedMask
    (m : CarrierVariable n → ℝ) (f : CarrierVariable n → ℂ) :
    regularizedCarrierIntegral d (parameterTruncatedMask Z m) f =
      regularizedCarrierIntegral d m f := by
  funext x
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u.1 ∈ Z
  · simp [parameterTruncatedMask, hu]
  · simp [carrierKernel_eq_zero_outside_parameters d hZ x u hu]

/-- The literal adjoint is zero off the angular parameter support, before
proving its uncut L² membership (`app:ch_background:eq:bg-realification`). -/
theorem carrierAdjointIntegral_eq_zero_outside_parameters
    (w : Torus n → EuclideanSpace ℂ (Fin n)) (u : CarrierVariable n) (hu : u.1 ∉ Z) :
    carrierAdjointIntegral d w u = 0 := by
  simp [carrierAdjointIntegral, carrierKernel_eq_zero_outside_parameters d hZ _ u hu]

variable {d} {m : CarrierVariable n → ℝ} {R M C : ℝ}
    (h : CarrierRegularization.MaskHypotheses d (parameterTruncatedMask Z m) Z R M C)

/-- The constructed compact operator realizes the original radial formula;
only the zero part of the kernel was removed (`app:ch_background:eq:bg-T`). -/
theorem parameterRegularizedOperator_ae (f : CarrierL2 n) :
    h.operator f =ᵐ[volume] regularizedCarrierIntegral d m f := by
  rw [← regularizedCarrierIntegral_parameterTruncatedMask d hZ m f]
  exact h.operator_ae f

/-- Its actual Hilbert adjoint also has the original radial formula
(`app:ch_background:eq:bg-realification`). -/
theorem parameterRegularizedOperator_adjoint_ae (w : ComplexOutputL2 n) :
    h.operator.adjoint w =ᵐ[carrierMeasure n]
      fun u ↦ (m u : ℂ) * carrierAdjointIntegral d w u := by
  filter_upwards [h.operator_adjoint_ae w] with u hu
  rw [hu]
  by_cases hz : u.1 ∈ Z
  · simp [parameterTruncatedMask, hz]
  · simp [carrierAdjointIntegral_eq_zero_outside_parameters d hZ w u hz]

/-- Finite-band bounds for the radial kernel, derived from the actual compact
operator's primitive hypotheses and the angular support
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def finiteCarrierKernelBoundsOfParameterMask : FiniteCarrierKernelBounds d m := by
  let hb := finiteCarrierKernelBoundsOfMask h
  have he := maskedCarrierKernel_parameterTruncatedMask d hZ m
  exact {
    carrierSupport := hb.carrierSupport
    isCompact_carrierSupport := hb.isCompact_carrierSupport
    frequencyRadius := hb.frequencyRadius
    frequencyRadius_nonneg := hb.frequencyRadius_nonneg
    bound := hb.bound
    bound_nonneg := hb.bound_nonneg
    stronglyMeasurable := by simpa only [← he] using hb.stronglyMeasurable
    norm_le := by simpa only [← he] using hb.norm_le
    eq_zero := by simpa only [← he] using hb.eq_zero }

/-- The normal of the ACTUAL compact operator has the original radial matrix
kernel, permitting the existing `ChartInputs` and `SymbolInputs` with no false
compact-support premise on a nonzero purely radial mask
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem parameterRegularizedOperator_normal_eq_matrix (w : ComplexOutputL2 n) :
    ∀ᵐ x ∂volume, ∀ i, h.operator (h.operator.adjoint w) x i =
      ∑ j, ∫ y, regularizedNormalEntry d m x y i j * w y j :=
  carrierHilbertNormal_eq_matrix (finiteCarrierKernelBoundsOfParameterMask hZ h)
    h.operator (parameterRegularizedOperator_ae hZ h) w
    (parameterRegularizedOperator_adjoint_ae hZ h w)

/-- The original radial normal pairing equals the pairing of the constructed
adjoints. This is the same carrier measure and radial density consumed by the
source convergence proof (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem parameterRegularizedOperator_normalTestPairing (v w : ComplexOutputL2 n) :
    normalTestPairing d m v w = inner ℂ (h.operator.adjoint v) (h.operator.adjoint w) :=
  normalTestPairing_eq_adjoint_inner (finiteCarrierKernelBoundsOfParameterMask hZ h)
    h.operator (parameterRegularizedOperator_ae hZ h) v w
    (parameterRegularizedOperator_adjoint_ae hZ h w)

end JanetCartan.ContinuumRow.CarrierNormalRealization
