module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.KernelAdapter
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedKernel.Coefficients

/-!
# The canonical kernel with refined masks and the retained outer inverse

This adapter consumes the outer smoothness, buffered inverse, transverse bound
and Jacobian gap supplied by `exists_actual_refined_supported_geometry`. The
physical and angular masks use its smaller radii `a'` and `r'`; every chart,
inverse, phase and determinant retains the original outer radii `a` and `r`.
The separate normal/detector smoothness inputs are produced by
`CanonicalBudgets`/`ActualAmplitude`, with domain matching left to the parent.

Consumer: `CarrierNormalRealization.exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`
(`app:ch_background:eq:bg-Psi`, `bg-jacobian`, `bg-full-complex-amplitude`,
`app:ch_background:defn:bg-row`). No transformed support, substitution identity,
chart conclusion or norm estimate is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option quotPrecheck false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol TransportKernel
open CarrierNormalRealization

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r')
    (hcell' : 4 * a' < 1 / 2)

local notation "d" => data T Q F row col Φ Y initial ha' hcell'
  (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
  FixedCutoffs.highFrequency

variable {c C : ℝ} (hP : P.IsValid c C)
    (haR : 6 * a < T.family.radius) (houter : 6 * a ≤ 3 * r)
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
    (hnormal : ContDiffOn ℝ ∞ (Function.uncurry (normalField T Q F row col Φ Y initial))
      (coefficientDomain z₀ r (6 * a)))
    (hdetector : ∀ i : Fin n, ContDiffOn ℝ ∞
      (fun p : Euclidean n × CarrierParameter ↦
        quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2)) i)
      (coefficientDomain z₀ r (6 * a)))

/-- The literal kernel substitution for every radial regularization of the
SAME canonical data. All geometry fields are proved from the retained chart;
the normal/detector input is precisely the primitive regularity supplied by
`CanonicalBudgets` (`app:ch_background:eq:bg-full-complex-amplitude`). -/
def refinedKernelChartInputs (R : ℝ) (x y : Torus n)
    (hx : x ∈ (d).outputChart) (hy : y ∈ (d).outputChart) :
    ChartInputs d (radialCarrierMask FixedCutoffs.radialRegularization R) x y where
  coordinates := kernelSliceCoordinates T
  measure_preserving := kernelSliceCoordinates_measurePreserving T
  domain := kernelDomain T z₀ ηb r (6 * a) ((d).chartPoint x) ((d).chartPoint y)
  phaseMap := kernelForward T Q ((d).chartPoint x) ((d).chartPoint y)
  inverse := kernelInverse T Q z₀ ηb r (6 * a) ((d).chartPoint x) ((d).chartPoint y)
  derivative := fun v t ↦ symbolDifferential T Q
    (kernelInput T ((d).chartPoint x) ((d).chartPoint y) v t)
  domain_measurable := fun v ↦ (kernelDomain_open T _ _ v).measurableSet
  has_derivative := fun v t ht ↦
    (kernelForward_hasFDerivAt T Q hηb hr hf _ _ v ht).hasFDerivWithinAt
  injective := fun v ↦ kernelForward_injective T Q hηb hr hInv htrans _ _ v
  left_inverse := fun v _ ht ↦ kernelInverse_forward T Q hηb hr hInv htrans _ _ v ht
  determinant_ne_zero := by
    intro v t ht
    have hj := symbolJacobian_eq_actual T Q hηb hr hf ht
    have hp := transportAbsoluteJacobian_pos T Q hηb hr hf hInv htrans hcJ ht
    rw [← hj] at hp
    exact abs_pos.mp hp
  support := fun v t ht i j ↦
    normalDensityEntry_zero_outside_symbolInputDomain T Q F row col Φ Y initial
      hηb hr' ha' har' hcell' _ _ x y hx hy _
      (fun hp ↦ ht (symbolInputDomain_mono z₀ ηb hrr
        (mul_le_mul_of_nonneg_left haa (by norm_num)) hp)) i j
  phase_identity := by
    intro v t ht
    have he := phase_identity_on_symbolInputDomain T Q hP hr haR houter hcarrier
      (p := kernelInput T ((d).chartPoint x) ((d).chartPoint y) v t) ht
    exact he
  density_measurable := fun i j ↦ refined_normalDensityEntry_measurable T Q F row col Φ Y initial
    hηb hr' ha' hcell' hnormal hdetector hrr haa har' R x y hx hy i j
  inverse_measurable := kernelInverse_measurable T Q hηb hr hInv htrans hV hLV _ _
  determinant_measurable := (symbolDeterminant_measurable T Q).comp
    (kernelInput_smooth T _ _).continuous.measurable
  image_measurable := kernelImage_measurable T Q hηb hr hInv htrans hV hLV _ _

/-- The exact symbol adapter uses the same inverse, determinant and conic
image for every regularization radius. Compact support and its image buffer
are derived from the original masks (`bg-full-complex-amplitude`). -/
def refinedKernelSymbolInputs {R : ℝ} (hR : 0 < R) (x y : Torus n)
    (hx : x ∈ (d).outputChart) (hy : y ∈ (d).outputChart) :
    SymbolInputs (refinedKernelChartInputs T Q F row col Φ Y initial hηb hr hr' ha' hrr haa har' hcell'
      hP haR houter hcarrier hf hInv htrans hV hLV hcJ hnormal hdetector R x y hx hy) where
  measurement := FixedCutoffs.physical ha' 1
  radial := FixedCutoffs.radialRegularization
  radius := R
  mask_eq := rfl
  measurement_left := rfl
  measurement_right := rfl
  jacobian := symbolJacobian T Q
  inverse := symbolInverse T Q z₀ ηb r (6 * a)
  forward := augmentedTransportGradient (transportPosition T Q)
  domain := symbolDomain T Q z₀ ηb r (6 * a)
  inputDomain := symbolInputDomain z₀ ηb r (6 * a)
  inputSupport := bandInputSupport z₀ ηb r' a' R
  spectatorSupport := closedBall (spectatorCenter z₀) (a' / 2)
  domain_open := symbolDomain_open T Q hηb hr hInv htrans hV hLV
  compact_spectator := isCompact_closedBall _ _
  angular_support := by
    intro z η hz
    change angularMask _ _ _ _ z η = 0
    by_contra h
    exact hz (ball_subset_closedBall
      (angularMask_nonzero z₀ (NormedSpace.normalize ηb) ha'
        (angularWidth_spec hηb hr').1 h).2.1)
  domain_eq := fun v k ↦ (kernel_image_iff T Q _ _ v k).symm
  inverse_eq := by
    intro v k
    exact ((adaptedSliceCoordinates T).equiv.apply_symm_apply _).symm
  jacobian_eq := by
    intro v k
    change symbolJacobian T Q _ = |(symbolDifferential T Q
      (kernelInput T _ _ v (kernelInverse T Q z₀ ηb r (6 * a) _ _ v k))).det|
    simp only [symbolJacobian, kernelInput, kernelInverse,
      ContinuousLinearEquiv.apply_symm_apply, inverseCoordinates]
  regularity := refined_regularizedCoefficients_regularity T Q F row col Φ Y initial
    hηb hr' ha' hcell' hnormal hdetector hr hf hInv htrans hcJ R
  inverse_smooth := symbolInverse_smooth T Q hηb hr hInv htrans hLV
  inverse_maps := symbolInverse_maps T Q hηb hr hInv htrans
  right_inverse := fun p hp ↦ augmentedTransportGradient_symbolInverse T Q hηb hr hInv htrans hp
  primitive_support := fun _ _ hx hy ha hhi ↦
    primitive_masks_mem_bandInputSupport hηb hr' _ hR hx hy ha hhi
  slice_closed := fun k ↦ refined_bandImage_slice_closed T Q hηb hr hr' ha' hrr haa har' hf _
  slice_buffer := fun _ _ hp ↦ refined_bandImage_subset_symbolDomain T Q hηb hr' ha' hrr haa har' hp

include hr hrr haa har' hP haR houter hcarrier hf hInv htrans hV hLV hcJ
  hnormal hdetector in
/-- The refined kernel families, with all same-object identities needed by
`exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`. For every
`R ≥ 1` the coefficients use the smaller original masks and finite band, while
the inverse, domain, forward map and Jacobian retain the outer chart. The
parent must instantiate the displayed geometric and primitive smoothness
hypotheses (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem exists_refined_kernel_inputs :
    ∃ charts : ∀ (R : ℝ), 1 ≤ R → ∀ x, x ∈ (d).outputChart →
        ∀ y, y ∈ (d).outputChart →
          ChartInputs d (radialCarrierMask FixedCutoffs.radialRegularization R) x y,
      ∃ symbols : ∀ R hR x hx y hy, SymbolInputs (charts R hR x hx y hy),
        ∀ R hR x hx y hy,
          (symbols R hR x hx y hy).coefficients = regularizedCoefficients
            (coefficientsOfCarrier d (FixedCutoffs.physical ha' 1))
              FixedCutoffs.radialRegularization R ∧
          (symbols R hR x hx y hy).jacobian = symbolJacobian T Q ∧
          (symbols R hR x hx y hy).inverse = symbolInverse T Q z₀ ηb r (6 * a) ∧
          (symbols R hR x hx y hy).domain = symbolDomain T Q z₀ ηb r (6 * a) ∧
          (symbols R hR x hx y hy).spectatorSupport = closedBall (spectatorCenter z₀) (a' / 2) ∧
          (symbols R hR x hx y hy).inputDomain = symbolInputDomain z₀ ηb r (6 * a) ∧
          (symbols R hR x hx y hy).inputSupport = bandInputSupport z₀ ηb r' a' R ∧
          (symbols R hR x hx y hy).forward =
            augmentedTransportGradient (transportPosition T Q) := by
  let charts := fun (R : ℝ) (_ : 1 ≤ R) (x : Torus n) hx (y : Torus n) hy ↦
    refinedKernelChartInputs T Q F row col Φ Y initial hηb hr hr' ha' hrr haa har' hcell'
      hP haR houter hcarrier hf hInv htrans hV hLV hcJ hnormal hdetector R x y hx hy
  let symbols := fun (R : ℝ) (hR : 1 ≤ R) (x : Torus n) hx (y : Torus n) hy ↦
    refinedKernelSymbolInputs T Q F row col Φ Y initial hηb hr hr' ha' hrr haa har' hcell'
      hP haR houter hcarrier hf hInv htrans hV hLV hcJ hnormal hdetector
        (zero_lt_one.trans_le hR) x y hx hy
  exact ⟨charts, symbols, fun _ _ _ _ _ _ ↦ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

end JanetCartan.ContinuumRow.CanonicalConic
