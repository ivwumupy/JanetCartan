module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.SupportedConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Amplitude

/-!
# Literal frozen-unit output on independently retained radii

This conclusion is proved by the local joint producer. It uses the outer
`r, 6*a` inverse, the inner `a', angularWidth ηb r'` mask and the original
Lebesgue spectator ball. The consuming parent assembles the Fourier energy
and spectral gap on these same choices (`bg-frame`, `bg-full-complex-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen.UnitRealization
open FrozenModel ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CarrierNormalRealization
open ContinuumNormalReduction TransportSymbol TransportKernel
open Pseudodifferential AmplitudeBound PeriodicLocalL2

/-- The full literal unit-carrier conclusion, with the exact separated symbol.
It is a conclusion of `exists_joint_carrier_normal_geometry_with_unit`, never
an analytic premise of the retained producer. Sources: `new:lem:scaling`,
`app:ch_background:eq:bg-full-complex-amplitude`, `app:ch_background:prop:bg-frame`. -/
def UnitCarrierOutput {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z₀ : Euclidean 3) (ηb : Euclidean (n - 1))
    (r a r' a' : ℝ) (hr' : 0 < r') (ha' : 0 < a') (hcell' : 4 * a' < 1 / 2)
    (hηb : ηb ≠ 0) (s : ℕ) (hs : 2 * (n + 1) ≤ s) : Prop :=
  let e := normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) ha' hcell'
    (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
    FixedCutoffs.highFrequency 0
  let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
  let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0)
  let u := frozenSymbolInverse T Q z₀ ηb r (6 * a)
  let Ω := frozenSymbolDomain T Q z₀ ηb r (6 * a)
  let S := closedBall (spectatorCenter z₀) (a' / 2)
  ∃ hn : 0 < n,
  ∃ hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a',
  ∃ B > (0 : ℝ),
  ∃ (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude d J u Ω S)))
    (hA : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude d J u Ω S ξ z i j) s B),
  ∃ Vcarrier : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
    (∀ v : carrierInitialTestSpace n,
      Vcarrier (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) ∧
    (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → Vcarrier f x = 0) ∧
    (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ v : carrierInitialTestSpace n,
        W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) → W = Vcarrier) ∧
    (∀ w : ComplexOutputL2 n,
      MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
      Vcarrier.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) ∧
    (realQuadratureChannel Vcarrier).comp (realQuadratureChannel Vcarrier).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn (4 * a') (fullReflectedMatrixAmplitude d J u Ω S) hb
          (fullReflectedMatrixAmplitude_supportedInCenteredBox d J u Ω S (4 * a') hsupport)
          B (fun i j ξ is his ↦ hA i j ξ is (his.trans hs)))) ∧
    ∀ ξ x y i j,
      fullReflectedMatrixAmplitude d J u Ω S ξ (pairedPosition x y) i j =
        (FixedCutoffs.physical ha' 1 x : ℂ) * (FixedCutoffs.physical ha' 1 y : ℂ) *
        (frozenCarrierSymbol T Q F row col Φ Y (fun _ ↦ 1)
          (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
          FixedCutoffs.highFrequency (adaptedSliceCoordinates T) u Ω S
          ((2 * Real.pi) • ξ) i j : ℂ)

end JanetCartan.ContinuumNormal.RetainedFrozen.UnitRealization
