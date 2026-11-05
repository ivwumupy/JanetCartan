module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Realization.Coefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.KernelAdapter

/-!
# The original slice chart for the frozen kernel

The slice substitution at zero scale is the original canonical slice map at
both physical positions zero. Its measurable determinant extension agrees
with the literal frozen Jacobian on the original input cone. This is the
same extension convention used by `CanonicalConic.kernelSymbolInputs`;
the equality of the resulting amplitudes with the literal Jacobian is proved
below. Consumer: the supported frozen carrier construction in
`app:ch_background:prop:bg-frame`, `bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol TransportKernel

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Globally measurable extension of the actual frozen slice determinant.
It is the retained canonical determinant at zero physical positions; no
Jacobian bound is part of this definition (`bg-jacobian`). -/
def frozenKernelJacobian (p : InputVariables n) : ℝ :=
  symbolJacobian T Q (originInput p)

/-- Measurability of the frozen determinant extension, without a global
smoothness assumption on the Hamilton phase (`bg-jacobian`). -/
theorem frozenKernelJacobian_measurable : Measurable (frozenKernelJacobian T Q) :=
  continuous_abs.measurable.comp ((symbolDeterminant_measurable T Q).comp
    originInput_smooth.continuous.measurable)

variable {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    {c C : ℝ} (hP : P.IsValid c C) (hηb : ηb ≠ 0) (hr : 0 < r)
    (har : a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ a ×ˢ dataSet z₀ ηb (3 * r)))

include hP hηb hr har hcarrier hf

/-- On the unchanged frozen input cone the measurable kernel determinant is
exactly the literal zero-scale transport Jacobian (`bg-jacobian`). -/
theorem frozenKernelJacobian_eq_actual :
    EqOn (frozenKernelJacobian T Q)
      (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q 0)) (frozenInputDomain z₀ ηb r a) := by
  intro p hp
  rw [frozenKernelJacobian, symbolJacobian_eq_actual T Q hηb hr hf hp,
    frozenJacobian_eq_origin T Q hP hr har hcarrier _ hp]

omit hf hηb in
/-- The actual frozen phase difference is the original slice forward map
at physical zero, on its retained input cone (`new:lem:scaling`, `bg-Psi`).
There is no restriction on the two output positions. -/
theorem frozenKernel_coordinate_phase_identity (x y : Euclidean n) (v : Euclidean 2)
    {t : Euclidean n} (ht : t ∈ kernelDomain T z₀ ηb r a 0 0 v) :
    inner ℝ (normalizedTransportPosition T Q 0
        (x, (chartCarrierVariable (kernelSliceCoordinates T) v t).1))
        (chartCarrierVariable (kernelSliceCoordinates T) v t).2 -
      inner ℝ (normalizedTransportPosition T Q 0
        (y, (chartCarrierVariable (kernelSliceCoordinates T) v t).1))
        (chartCarrierVariable (kernelSliceCoordinates T) v t).2 =
      inner ℝ (x - y) (kernelForward T Q 0 0 v t) := by
  have hz := phaseBuffer_of_frozenInputDomain T hr hP har hcarrier
    (p := kernelInput T 0 0 v t) ht
  dsimp only [kernelInput] at hz
  change inner ℝ (normalizedTransportPosition T Q 0
        (x, (((adaptedSliceCoordinates T).equiv t).1, v)))
        ((adaptedSliceCoordinates T).equiv t).2 -
      inner ℝ (normalizedTransportPosition T Q 0
        (y, (((adaptedSliceCoordinates T).equiv t).1, v)))
        ((adaptedSliceCoordinates T).equiv t).2 = _
  rw [normalizedTransportPhase_zero T Q hz, normalizedTransportPhase_zero T Q hz,
    ← inner_sub_left]
  congr 1
  exact (transportAveragedGradient_zero T Q (kernelInput T 0 0 v t) hz).symm.trans
    (frozenForward_eq_origin T Q hP hr har hcarrier (p := kernelInput T 0 0 v t) ht)

variable {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ a,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hInv htrans

/-- The determinant extension leaves every frozen density unchanged,
including its zero extension outside the actual symbol domain. This connects
the supported kernel constructor to the SAME spectral symbol
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenKernel_extendedDensity_eq_actual {N : ℕ} (d : Coefficients n N)
    (p : Variables n × Euclidean 2) :
    extendedDensity d (frozenKernelJacobian T Q)
      (frozenSymbolInverse T Q z₀ ηb r a) (frozenSymbolDomain T Q z₀ ηb r a) p =
    extendedDensity d (transportAbsoluteJacobian (adaptedSliceCoordinates T)
      (normalizedTransportPosition T Q 0))
      (frozenSymbolInverse T Q z₀ ηb r a) (frozenSymbolDomain T Q z₀ ηb r a) p := by
  classical
  by_cases hp : p ∈ frozenSymbolDomain T Q z₀ ηb r a
  · simp only [extendedDensity, indicator_of_mem hp, inputDensity, inputWeight]
    rw [frozenKernelJacobian_eq_actual T Q hP hηb hr har hcarrier hf
      (frozenSymbolInverse_maps T Q hηb hr hInv htrans hp)]
  · simp only [extendedDensity, indicator_of_notMem hp]

/-- Equality of the full reflected amplitudes, preserving both real
quadratures and the physical `2π` normalization. The measurable determinant
extension therefore does not change the Fourier consumer's literal symbol
(`bg-full-complex-amplitude`, `bg-real-symbol`). -/
theorem frozenKernel_fullReflectedMatrixAmplitude_eq_actual {N : ℕ}
    (d : Coefficients n N) (S : Set (Euclidean 2)) :
    CarrierNormalRealization.fullReflectedMatrixAmplitude d (frozenKernelJacobian T Q)
      (frozenSymbolInverse T Q z₀ ηb r a) (frozenSymbolDomain T Q z₀ ηb r a) S =
    CarrierNormalRealization.fullReflectedMatrixAmplitude d
      (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0))
      (frozenSymbolInverse T Q z₀ ηb r a) (frozenSymbolDomain T Q z₀ ηb r a) S := by
  have he := fun p ↦ frozenKernel_extendedDensity_eq_actual T Q hP hηb hr har hcarrier hf
    hInv htrans d p
  funext ξ z
  unfold CarrierNormalRealization.fullReflectedMatrixAmplitude
  unfold reflectedSymbolAmplitude TransportSymbol.amplitude
  simp_rw [he]

end JanetCartan.ContinuumNormal.FrozenModel
