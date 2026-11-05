module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Assembly
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.FourierIdentity

/-!
# Fourier interface for the constructed frozen spectral data

The local geometry returned by `exists_finite_frozen_spectral_gap` discharges
the measurable bounded symbol and amplitude-separation inputs of the Fourier
consumer. The remaining premises below are precisely the full-amplitude
regularity, derivative bounds, global normal and initial-test identities
produced by the supported primitive carrier realization. This implication is
independent of that construction and does not assert existence of an extension.
The same inverse, masks, spectator measure and measured carrier appear on both
sides (`app:ch_background:prop:bg-frame`, frozen Plancherel step).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory Matrix
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CarrierNormalRealization
open ContinuumNormalReduction TransportSymbol TransportKernel ConicChart
open AmplitudeBound Pseudodifferential PeriodicLocalL2

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}
    (d : FrozenIncidencePatchData T z₀ ηb)
    {c C : ℝ} (hP : P.IsValid c C) (hgeom : d.Geometry Q)
    (F : Euclidean n → Euclidean N)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {ρ : ℝ} (hρ : 0 < ρ) (hcell : 4 * ρ < 1 / 2)

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) d.ha
  (And.left (angularWidth_spec d.hηb d.hr))
local notation "e₀" => normalizedCarrierData T Q F d.row d.col Φ Y (fun _ ↦ 1)
  hρ hcell angular₀ FixedCutoffs.highFrequency 0
local notation "a₀" => coefficientsOfCarrier e₀ (FixedCutoffs.physical hρ 1)
local notation "J₀" => transportAbsoluteJacobian (adaptedSliceCoordinates T)
  (normalizedTransportPosition T Q 0)
local notation "u₀" => frozenSymbolInverse T Q z₀ ηb d.r (6 * d.a)
local notation "Ω₀" => frozenSymbolDomain T Q z₀ ηb d.r (6 * d.a)
local notation "S₀" => closedBall (spectatorCenter z₀) (d.a / 2)
local notation "b₀" => canonicalFrozenCarrierSymbol T Q F d.row d.col Φ Y (fun _ ↦ 1)
  z₀ d.hηb d.hr d.ha

include hP hgeom

/-- The exact canonical unit-amplitude symbol has the Fourier energy of any
extension of its literal zero-scale carrier, once the primitive realization's
normal and test identities have been supplied. All spectral inputs are proved
from the SAME local geometry constructed in `exists_finite_frozen_spectral_gap`.
The measurement radius may be common to the finite family and independent of
the individual angular radii. Actual production of the operator hypotheses is
owned by `Spectral.PrimitiveRealization`, through
`exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`
(`new:lem:scaling`, `app:ch_background:prop:bg-frame`). -/
theorem canonicalFrozenCarrierExtension_adjoint_norm_sq_eq_energy_unit
    (hn : 0 < n) (R : ℝ)
    (hsupport : ∀ x, FixedCutoffs.physical (n := n) hρ 1 x ≠ 0 → ∀ j, |x j| ≤ R)
    (hA : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude a₀ J₀ u₀ Ω₀ S₀)))
    (B : ℝ) (hB : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude a₀ J₀ u₀ Ω₀ S₀ ξ z i j) (2 * (n + 1)) B)
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hV : (realQuadratureChannel V).comp (realQuadratureChannel V).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn R (fullReflectedMatrixAmplitude a₀ J₀ u₀ Ω₀ S₀) hA
          (fullReflectedMatrixAmplitude_supportedInCenteredBox a₀ J₀ u₀ Ω₀ S₀ R hsupport) B hB)))
    (hVtest : ∀ v : carrierInitialTestSpace n,
      V (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e₀ v.val)
    (W : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hWtest : ∀ v : carrierInitialTestSpace n,
      W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e₀ v.val)
    (w : OutputL2 n) :
    ‖(realQuadratureChannel W).adjoint w‖ ^ 2 =
      euclideanFrozenEnergy b₀ (fun x ↦ euclideanComplexInclusion
        (FixedCutoffs.physical hρ 1 x • toEuclidean (𝕜 := ℝ) w x)) := by
  have har : 6 * d.a ≤ 3 * d.r := by linarith [d.har, d.hr]
  have hcont := canonicalFrozenCarrierSymbol_unit_continuous T Q F d.row d.col Φ Y
    hP d.hηb d.hr d.ha har d.hcarrier hgeom.1 hgeom.2.2.1 hgeom.2.2.2 d.hcJ d.hV d.hLV
  obtain ⟨C, _, hC⟩ := canonicalFrozenCarrierSymbol_unit_bounded T Q F d.row d.col Φ Y
    hP d.hηb d.hr d.ha har d.hcarrier hgeom.1 hgeom.2.2.1 hgeom.2.2.2 d.hcJ
  have hb (i j : Fin n) : Measurable (fun k ↦ b₀ k i j) :=
    ((continuous_apply j).comp ((continuous_apply i).comp hcont)).measurable
  have hsep (ξ x y : Euclidean n) (i j : Fin n) :
      fullReflectedMatrixAmplitude a₀ J₀ u₀ Ω₀ S₀ ξ (pairedPosition x y) i j =
        (FixedCutoffs.physical hρ 1 x : ℂ) * (FixedCutoffs.physical hρ 1 y : ℂ) *
          (b₀ ((2 * Real.pi) • ξ) i j : ℂ) := by
    have hh := fullReflectedMatrixAmplitude_normalizedCarrierData_zero T Q F d.row d.col Φ Y
      (fun _ ↦ 1) angular₀ FixedCutoffs.highFrequency (adaptedSliceCoordinates T)
      hP d.hηb d.hr har d.hcarrier hgeom.2.2.1 hgeom.2.2.2 hρ hcell S₀ x y ξ
    simpa only [canonicalFrozenCarrierSymbol, Pi.smul_apply, Complex.real_smul, Complex.ofReal_mul] using
      congrArg (fun m ↦ m i j) hh
  exact carrierExtension_adjoint_norm_sq_eq_frozenCarrierEnergy T Q F d.row d.col Φ Y
    (fun _ ↦ 1) hρ hcell angular₀ FixedCutoffs.highFrequency (adaptedSliceCoordinates T)
    u₀ Ω₀ S₀ hn R hsupport hA B hB hb C hC hsep V hV hVtest W hWtest w

end JanetCartan.ContinuumNormal.FrozenModel
