module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Kernel.FiniteInputs
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Kernel.Support

/-!
# Literal frozen kernel and symbol inputs

The original unit-initial normalized carrier is used at scale zero. Its
physical and angular masks use the smaller radii, while the inverse and its
domain retain the outer radii. All chart, density, phase and regularity fields
are proved from the geometric outputs of `exists_frozen_conic_inputs` and the
refined radius inequalities. The parent applies
`exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`.

Sources: `new:lem:scaling`, `app:ch_background:eq:bg-full-complex-amplitude`,
and `app:ch_background:prop:bg-frame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r')
    (hcell' : 4 * a' < 1 / 2)

local notation "e₀" => normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) ha' hcell'
  (angularMask z₀ (NormedSpace.normalize ηb) ha' (And.left (angularWidth_spec hηb hr')))
  FixedCutoffs.highFrequency 0

variable {c C : ℝ} (hP : P.IsValid c C)
    (houter : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hV : IsOpen V) (hLV : L ⊆ V) (hcJ : 0 < cJ)

/-- Construct the literal frozen carrier's substitution chart for every
radial regularization, with refined masks, the original slice measure and phase
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def frozenRefinedKernelChartInputs (R : ℝ) (x y : Torus n) :
    ChartInputs e₀ (radialCarrierMask FixedCutoffs.radialRegularization R) x y where
  coordinates := kernelSliceCoordinates T
  measure_preserving := kernelSliceCoordinates_measurePreserving T
  domain := frozenKernelDomain T z₀ ηb r (6 * a) ((e₀).chartPoint x) ((e₀).chartPoint y)
  phaseMap := frozenKernelForward T Q ((e₀).chartPoint x) ((e₀).chartPoint y)
  inverse := frozenKernelInverse T Q z₀ ηb r (6 * a) ((e₀).chartPoint x) ((e₀).chartPoint y)
  derivative := fun v t ↦ frozenKernelDifferential T Q z₀ ηb r (6 * a)
    (kernelInput T ((e₀).chartPoint x) ((e₀).chartPoint y) v t)
  domain_measurable := fun v ↦ (frozenKernelDomain_open T _ _ v).measurableSet
  has_derivative := fun v t ht ↦
    (frozenKernelForward_hasFDerivAt T Q hP hηb hr houter hcarrier hf _ _ v ht).hasFDerivWithinAt
  injective := fun v ↦ frozenKernelForward_injective T Q hP hηb hr houter hcarrier hInv htrans _ _ v
  left_inverse := fun v _ ht ↦
    frozenKernelInverse_forward T Q hP hηb hr houter hcarrier hInv htrans _ _ v ht
  determinant_ne_zero := by
    intro v t ht
    have hj := frozenKernelDifferential_det T Q hP hηb hr houter hcarrier hf ht
    have hp := frozenJacobian_pos T Q hP hηb hr houter hcarrier hInv htrans hf hcJ ht
    rw [← hj] at hp
    exact abs_pos.mp hp
  support := fun v t ht i j ↦
    frozenNormalDensityEntry_zero_outside T Q F row col Φ Y
      hηb hr' ha' hcell' hrr haa har' _ x y _ ht i j
  phase_identity := by
    intro v t ht
    have he := frozenKernel_input_phase_identity T Q hP hr houter hcarrier
      (p := kernelInput T ((e₀).chartPoint x) ((e₀).chartPoint y) v t) ht
    exact he
  density_measurable := fun i j ↦ frozenNormalDensityEntry_measurable T Q F row col Φ Y
    hηb hr' ha' hcell' hP hr houter hcarrier hrr haa har' R x y i j
  inverse_measurable := frozenKernelInverse_measurable T Q hηb hr hInv htrans hV hLV _ _
  determinant_measurable := (frozenKernelDeterminant_measurable T Q z₀ ηb r (6 * a)).comp
    (kernelInput_smooth T _ _).continuous.measurable
  image_measurable :=
    frozenKernelImage_measurable T Q hP hηb hr houter hcarrier hInv htrans hV hLV _ _

/-- The refined-mask symbol input uses the literal normalized transport Jacobian, the
retained frozen inverse, and the original Lebesgue spectator ball. Both
measurements and the radial mask remain in the coefficients
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def frozenRefinedKernelSymbolInputs {R : ℝ} (hR : 0 < R) (x y : Torus n) :
    SymbolInputs (frozenRefinedKernelChartInputs T Q F row col Φ Y hηb hr hr' ha' hrr haa har' hcell'
      hP houter hcarrier hf hInv htrans hV hLV hcJ R x y) where
  measurement := FixedCutoffs.physical ha' 1
  radial := FixedCutoffs.radialRegularization
  radius := R
  mask_eq := rfl
  measurement_left := rfl
  measurement_right := rfl
  jacobian := transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0)
  inverse := frozenSymbolInverse T Q z₀ ηb r (6 * a)
  forward := augmentedTransportGradient (normalizedTransportPosition T Q 0)
  domain := frozenSymbolDomain T Q z₀ ηb r (6 * a)
  inputDomain := frozenInputDomain z₀ ηb r (6 * a)
  inputSupport := bandInputSupport z₀ ηb r' a' R
  spectatorSupport := closedBall (spectatorCenter z₀) (a' / 2)
  domain_open := frozenSymbolDomain_open T Q hηb hr hInv htrans hV hLV
  compact_spectator := isCompact_closedBall _ _
  angular_support := by
    intro z η hz
    change angularMask _ _ _ _ z η = 0
    by_contra h
    exact hz (ball_subset_closedBall
      (angularMask_nonzero z₀ (NormedSpace.normalize ηb) ha'
        (And.left (angularWidth_spec hηb hr')) h).2.1)
  domain_eq := fun v k ↦
    (frozenKernel_image_iff T Q hP hηb hr houter hcarrier hInv htrans _ _ v k).symm
  inverse_eq := fun _ _ ↦ ((adaptedSliceCoordinates T).equiv.apply_symm_apply _).symm
  jacobian_eq := by
    intro v k
    change _ = |(frozenKernelDifferential T Q z₀ ηb r (6 * a)
      (kernelInput T _ _ v (frozenKernelInverse T Q z₀ ηb r (6 * a) _ _ v k))).det|
    simp only [kernelInput, frozenKernelInverse, ContinuousLinearEquiv.apply_symm_apply]
    exact frozenKernel_inverse_jacobian T Q hP hηb hr houter hcarrier hf hInv htrans
      (Nat.zero_lt_of_lt row.isLt) _
  regularity := frozenRefined_regularizedCoefficients_regularity T Q F row col Φ Y
    hηb hr' ha' hcell' hP hr houter hcarrier hf hInv htrans hcJ R
  inverse_smooth := frozenSymbolInverse_smooth T Q hηb hr hInv htrans hLV
  inverse_maps := frozenSymbolInverse_maps T Q hηb hr hInv htrans
  right_inverse := fun _ hp ↦
    augmentedFrozenGradient_inverse T Q hP hηb hr houter hcarrier hInv htrans hp
  primitive_support := fun _ _ hx hy ha hhi ↦
    primitive_masks_mem_bandInputSupport hηb hr' _ hR hx hy ha hhi
  slice_closed := fun k ↦
    frozenRefined_bandImage_slice_closed T Q hP hηb hr hr' ha' hrr haa har' houter hcarrier hf _
  slice_buffer := fun _ _ hp ↦
    frozenRefined_bandImage_subset_symbolDomain T Q hP hηb hr hr' ha' hrr haa har'
      houter hcarrier hInv htrans hp

include hr hrr haa har' hP houter hcarrier hf hInv htrans hV hLV hcJ in
/-- Every `R ≥ 1` has the exact kernel and symbol inputs required by
`exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`.
The radius-independent identities preserve the literal Jacobian, inverse,
domain, forward map and original spectator measure. Normal and detector
regularity are proved from the seed (`new:lem:scaling`, `bg-full-complex-amplitude`). -/
theorem exists_frozen_refined_kernel_inputs :
    ∃ charts : ∀ (R : ℝ), 1 ≤ R → ∀ x, x ∈ (e₀).outputChart →
        ∀ y, y ∈ (e₀).outputChart →
          ChartInputs e₀ (radialCarrierMask FixedCutoffs.radialRegularization R) x y,
      ∃ symbols : ∀ R hR x hx y hy, SymbolInputs (charts R hR x hx y hy),
        ∀ R hR x hx y hy,
          (symbols R hR x hx y hy).coefficients = regularizedCoefficients
            (coefficientsOfCarrier e₀ (FixedCutoffs.physical ha' 1))
              FixedCutoffs.radialRegularization R ∧
          (symbols R hR x hx y hy).jacobian =
            transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0) ∧
          (symbols R hR x hx y hy).inverse = frozenSymbolInverse T Q z₀ ηb r (6 * a) ∧
          (symbols R hR x hx y hy).domain = frozenSymbolDomain T Q z₀ ηb r (6 * a) ∧
          (symbols R hR x hx y hy).spectatorSupport = closedBall (spectatorCenter z₀) (a' / 2) ∧
          (symbols R hR x hx y hy).inputDomain = frozenInputDomain z₀ ηb r (6 * a) ∧
          (symbols R hR x hx y hy).inputSupport = bandInputSupport z₀ ηb r' a' R ∧
          (symbols R hR x hx y hy).forward =
            augmentedTransportGradient (normalizedTransportPosition T Q 0) := by
  let charts := fun (R : ℝ) (_ : 1 ≤ R) (x : Torus n) (_ : x ∈ (e₀).outputChart)
      (y : Torus n) (_ : y ∈ (e₀).outputChart) ↦
    frozenRefinedKernelChartInputs T Q F row col Φ Y hηb hr hr' ha' hrr haa har' hcell'
      hP houter hcarrier hf hInv htrans hV hLV hcJ R x y
  let symbols := fun (R : ℝ) (hR : 1 ≤ R) (x : Torus n) (_ : x ∈ (e₀).outputChart)
      (y : Torus n) (_ : y ∈ (e₀).outputChart) ↦
    frozenRefinedKernelSymbolInputs T Q F row col Φ Y hηb hr hr' ha' hrr haa har' hcell'
      hP houter hcarrier hf hInv htrans hV hLV hcJ (zero_lt_one.trans_le hR) x y
  exact ⟨charts, symbols, fun _ _ _ _ _ _ ↦ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

end JanetCartan.ContinuumNormal.FrozenModel
