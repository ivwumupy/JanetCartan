module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.FourierMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.CanonicalConstruction

/-!
# The exact local realization conclusion for finite spectral assembly

This predicate names the output proved by `exists_realized_frozen_incidence_patch`.
It is not an assumed construction field. The same `FrozenIncidencePatchData`
supplies the inverse, mask, spectator ball, minor and geometric frequency radius
used by the finite gap and Fourier consumers (`app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CarrierNormalRealization
open ContinuumNormalReduction TransportSymbol TransportKernel
open Pseudodifferential AmplitudeBound PeriodicLocalL2

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU} {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}

/-- The literal unit-initial carrier, its unique extension, adjoint, full normal
and Fourier energy, all on the SAME patch data. This is a proved conclusion of
`exists_realized_frozen_incidence_patch`, consumed by the finite realized cover;
common measurement restriction remains a separate proved matching operation
(`new:lem:scaling`, `app:ch_background:prop:bg-frame`). -/
def FrozenIncidencePatchData.UnitRealization (d : FrozenIncidencePatchData T z₀ ηb)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (hcell : 4 * d.a < 1 / 2) : Prop :=
  ∀ (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (s : ℕ) (hs : 2 * (n + 1) ≤ s),
  let e := normalizedCarrierData T Q F d.row d.col Φ Y (fun _ ↦ 1) d.ha hcell
    (angularMask z₀ (NormedSpace.normalize ηb) d.ha (angularWidth_spec d.hηb d.hr).1)
    FixedCutoffs.highFrequency 0
  let a := coefficientsOfCarrier e (FixedCutoffs.physical d.ha 1)
  let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0)
  let u := frozenSymbolInverse T Q z₀ ηb d.r (6 * d.a)
  let Ω := frozenSymbolDomain T Q z₀ ηb d.r (6 * d.a)
  let S := closedBall (spectatorCenter z₀) (d.a / 2)
  ∃ hn : 0 < n,
  ∃ hsupport : ∀ x, a.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * d.a,
  ∃ B > (0 : ℝ),
  ∃ (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S)))
    (hA : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j) s B),
  ∃ V : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
    (∀ v : carrierInitialTestSpace n,
      V (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) ∧
    (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → V f x = 0) ∧
    (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ v : carrierInitialTestSpace n,
        W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) → W = V) ∧
    (∀ w : ComplexOutputL2 n,
      MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
      V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) ∧
    (realQuadratureChannel V).comp (realQuadratureChannel V).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn (4 * d.a) (fullReflectedMatrixAmplitude a J u Ω S) hb
          (fullReflectedMatrixAmplitude_supportedInCenteredBox a J u Ω S (4 * d.a) hsupport)
          B (fun i j ξ is his ↦ hA i j ξ is (his.trans hs)))) ∧
    ∀ (W : CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ v : carrierInitialTestSpace n,
        W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) →
      ∀ w : OutputL2 n,
        ‖(realQuadratureChannel W).adjoint w‖ ^ 2 =
          euclideanFrozenEnergy
            (canonicalFrozenCarrierSymbol T Q F d.row d.col Φ Y (fun _ ↦ 1)
              z₀ d.hηb d.hr d.ha)
            (fun x ↦ euclideanComplexInclusion
              (FixedCutoffs.physical d.ha 1 x • toEuclidean (𝕜 := ℝ) w x))

end JanetCartan.ContinuumNormal.FrozenModel
