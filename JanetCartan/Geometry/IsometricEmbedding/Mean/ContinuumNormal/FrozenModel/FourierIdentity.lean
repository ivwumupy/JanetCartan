module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.FourierIdentity.MultiplierEnergy
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.FourierIdentity.SeparatedAmplitude

/-!
# Euclidean Fourier energy of the literal frozen carrier

For `app:ch_background:prop:bg-frame`, the full reflected amplitude separates
into the two original measurement factors and the bounded real matrix symbol.
`SeparatedAmplitude` proves its action first on smooth Euclidean tests, then on
all L² inputs by density. `MultiplierEnergy` proves the Plancherel identity and
integrability. Here the published global normal realization connects those
results to the SAME literal carrier extension and its real adjoint.

The smooth real torus test formula uses its measured Euclidean zero extension.
The all-data formula holds on the entire real torus L² space, hence on every
supported subspace. Initial-test density identifies every admissible choice of
extension. `carrierExtension_adjoint_norm_sq_eq_frozenCarrierEnergy` specializes
the result to `normalizedCarrierData` at zero and its actual `frozenCarrierSymbol`.
Both real quadratures, the reflected factor four, the original `carrierMeasure`,
and the Euclidean Lebesgue frequency measure with `k = 2πξ` are retained.

Consumer: `jc-frozen-continuum-model`. The global normal equality, amplitude
smoothness and derivative bounds are the outputs of
`CarrierNormalRealization.exists_carrierL2Extension_globalNormal_of_primitiveNorms`.
The measurable bounded symbol and full-amplitude separation are the explicit
inputs supplied by `jc-frozen-model-spectral`; they are not an assumed energy
identity. The parent retains their actual geometric instantiation and the
primitive carrier construction. These deductions alone do not assert coercivity.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Matrix
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.FrozenModel
open AmplitudeBound Pseudodifferential PeriodicLocalL2 ContinuumRow
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization

variable {n N : ℕ}

section GlobalNormal

variable (hn : 0 < n)
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hχc : ContDiff ℝ ∞ a.measurement) (hχs : HasCompactSupport a.measurement)
    (R : ℝ) (hsupport : ∀ x, a.measurement x ≠ 0 → ∀ j, |x j| ≤ R)
    (hA : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S)))
    (B : ℝ) (hB : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j) (2 * (n + 1)) B)
    (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hb : ∀ i j, Measurable (fun k ↦ b k i j))
    (C : ℝ) (hC : ∀ k, ‖b k‖ ≤ C)
    (hsep : ∀ ξ x y i j, fullReflectedMatrixAmplitude a J u Ω S ξ (pairedPosition x y) i j =
      (a.measurement x : ℂ) * (a.measurement y : ℂ) * (b ((2 * Real.pi) • ξ) i j : ℂ))
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : (realQuadratureChannel U).comp (realQuadratureChannel U).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn R (fullReflectedMatrixAmplitude a J u Ω S) hA
          (fullReflectedMatrixAmplitude_supportedInCenteredBox a J u Ω S R hsupport) B hB)))

include hχc hχs hb hC hsep hU

/-- The frozen Plancherel step for the SAME carrier whose global normal is
realized by the full reflected PDO (`app:ch_background:prop:bg-frame`).
The symbol is only required to be measurable and uniformly bounded; entrywise
L∞ membership and measurement integrability are derived. This holds for every
real torus L² input, in particular every supported input, with its actual measured
Euclidean zero extension. The normal hypothesis is precisely the published
primitive construction's output, before any Fourier-multiplier identification. -/
theorem realQuadratureAdjoint_norm_sq_eq_euclideanFrozenEnergy (w : OutputL2 n) :
    ‖(realQuadratureChannel U).adjoint w‖ ^ 2 =
      euclideanFrozenEnergy b
        (fun x ↦ euclideanComplexInclusion (a.measurement x • toEuclidean (𝕜 := ℝ) w x)) := by
  have hχ : MemLp (fun x ↦ (a.measurement x : ℂ)) ∞ volume :=
    (Complex.continuous_ofReal.comp hχc.continuous).memLp_top_of_hasCompactSupport
      (hχs.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)) volume
  have hentry := frozenSymbolEntry_memLp b hb C hC
  rw [realQuadratureAdjoint_norm_sq_eq_euclidean_pairing U _ hU w,
    vectorTwoPositionL2Operator_eq_frozenMeasuredMultiplier hn R a.measurement hχ hχc hχs
      b hentry _ hA _ B hB hsep,
    re_inner_frozenMeasuredMultiplier a.measurement hχ hχc.continuous hχs]
  apply euclideanFrozenEnergy_congr_ae
  exact (frozenMeasurementOperator_coeFn a.measurement hχ _).symm.trans
    (frozenMeasurementOperator_toEuclidean_coeFn a.measurement hχ w)

/-- On smooth real torus tests, the frozen energy is the Fourier integral of
the compactly supported physical source profile, equal almost everywhere to
the measured Euclidean zero extension (`app:ch_background:prop:bg-frame`).
This includes tests supported in the measurement chart. Compact measurement
support suffices even when the original periodic test has larger support. -/
theorem realQuadratureAdjoint_norm_sq_eq_frozenEnergy_smoothPeriodic
    (hcell : ∀ x ∉ halfOpenCell n, a.measurement x = 0)
    (w₀ : Torus n → Euclidean n) (hw₀ : IsSmoothPeriodic w₀) :
    ‖(realQuadratureChannel U).adjoint
      (PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0 w₀ hw₀))‖ ^ 2 =
      euclideanFrozenEnergy b
        (TestChartTransfer.physicalSourceProfile a.measurement
          (fun z ↦ euclideanComplexInclusion (w₀ z))) := by
  have hχ : MemLp (fun x ↦ (a.measurement x : ℂ)) ∞ volume :=
    (Complex.continuous_ofReal.comp hχc.continuous).memLp_top_of_hasCompactSupport
      (hχs.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)) volume
  rw [realQuadratureAdjoint_norm_sq_eq_euclideanFrozenEnergy hn a J u Ω S
    hχc hχs R hsupport hA B hB b hb C hC hsep U hU]
  apply euclideanFrozenEnergy_congr_ae
  exact (frozenMeasurementOperator_toEuclidean_coeFn a.measurement hχ _).symm.trans
    (frozenMeasurementOperator_toEuclidean_eq_physicalSourceProfile a.measurement hχ hcell
      _ w₀ (PeriodicSobolevSpace.toL2_ofSmooth_ae 0 w₀ hw₀))

/-- Every extension of the SAME literal action on `carrierInitialTestSpace`
has the frozen Euclidean energy (`app:ch_background:prop:bg-frame`).
Only the published realization `U` needs a global normal certificate: the
initial-test characterization proves `W = U`. Thus the energy does not depend
on the choice made in the primitive carrier existence theorem. -/
theorem carrierExtension_adjoint_norm_sq_eq_euclideanFrozenEnergy
    (e : CarrierData n N)
    (hUtest : ∀ v : carrierInitialTestSpace n,
      U (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val)
    (W : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hWtest : ∀ v : carrierInitialTestSpace n,
      W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val)
    (w : OutputL2 n) :
    ‖(realQuadratureChannel W).adjoint w‖ ^ 2 =
      euclideanFrozenEnergy b
        (fun x ↦ euclideanComplexInclusion (a.measurement x • toEuclidean (𝕜 := ℝ) w x)) := by
  rw [carrierExtensions_eq_of_initialTests e U W hUtest hWtest]
  exact realQuadratureAdjoint_norm_sq_eq_euclideanFrozenEnergy hn a J u Ω S
    hχc hχs R hsupport hA B hB b hb C hC hsep U hU w

end GlobalNormal

section FrozenCarrier

open ActualCarriers FrozenMenu CurrentFullPhase

variable {P : Patch n} {V : Set (Euclidean n)} {hV : IsOpen V}
    (T : PatchQuantitativeFamily P V hV)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q V ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (c : TransportSliceCoordinates n)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))

local notation "e₀" => normalizedCarrierData T Q F row col Φ Y initial hr hcell angular high 0
local notation "a₀" => coefficientsOfCarrier e₀ (FixedCutoffs.physical hr 1)
local notation "J₀" => transportAbsoluteJacobian c (normalizedTransportPosition T Q 0)
local notation "b₀" => frozenCarrierSymbol T Q F row col Φ Y initial angular high c u Ω S

/-- The literal zero-scale normalized carrier has the energy of its actual
`frozenCarrierSymbol`, for every admissible chosen extension and every real
output L² datum (`app:ch_background:prop:bg-frame`, frozen Plancherel step).

The measurement regularity is discharged by the existing physical bump. The
coefficients are those of this exact `normalizedCarrierData`; the theorem
`coefficientsOfCarrier_normalizedCarrierData_zero` identifies them with the
measured `uncutFrozenCoefficients` used by the spectral producer. The inverse,
absolute transport Jacobian, domain, spectator support, angular mask and high
mask are the SAME arguments on both sides. The parent supplies the spectral
bounds/separation and the primitive construction's normal and test certificates. -/
theorem carrierExtension_adjoint_norm_sq_eq_frozenCarrierEnergy
    (hn : 0 < n) (R : ℝ)
    (hsupport : ∀ x, FixedCutoffs.physical (n := n) hr 1 x ≠ 0 → ∀ j, |x j| ≤ R)
    (hA : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude a₀ J₀ u Ω S)))
    (B : ℝ) (hB : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude a₀ J₀ u Ω S ξ z i j) (2 * (n + 1)) B)
    (hb : ∀ i j, Measurable (fun k ↦ b₀ k i j))
    (C : ℝ) (hC : ∀ k, ‖b₀ k‖ ≤ C)
    (hsep : ∀ ξ x y i j, fullReflectedMatrixAmplitude a₀ J₀ u Ω S ξ (pairedPosition x y) i j =
      (FixedCutoffs.physical hr 1 x : ℂ) * (FixedCutoffs.physical hr 1 y : ℂ) *
        (b₀ ((2 * Real.pi) • ξ) i j : ℂ))
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : (realQuadratureChannel U).comp (realQuadratureChannel U).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn R (fullReflectedMatrixAmplitude a₀ J₀ u Ω S) hA
          (fullReflectedMatrixAmplitude_supportedInCenteredBox a₀ J₀ u Ω S R hsupport) B hB)))
    (hUtest : ∀ v : carrierInitialTestSpace n,
      U (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e₀ v.val)
    (W : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hWtest : ∀ v : carrierInitialTestSpace n,
      W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e₀ v.val)
    (w : OutputL2 n) :
    ‖(realQuadratureChannel W).adjoint w‖ ^ 2 =
      euclideanFrozenEnergy b₀ (fun x ↦ euclideanComplexInclusion
        (FixedCutoffs.physical hr 1 x • toEuclidean (𝕜 := ℝ) w x)) := by
  exact carrierExtension_adjoint_norm_sq_eq_euclideanFrozenEnergy hn a₀ J₀ u Ω S
    (FixedCutoffs.physical hr 1).contDiff (FixedCutoffs.physical hr 1).hasCompactSupport
    R hsupport hA B hB b₀ hb C hC hsep U hU e₀ hUtest W hWtest w

end FrozenCarrier
end JanetCartan.ContinuumNormal.FrozenModel
