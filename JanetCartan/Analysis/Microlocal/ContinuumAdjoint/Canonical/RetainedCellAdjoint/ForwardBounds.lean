module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RetainedCellAdjoint.Geometry
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RetainedCellAdjoint.Profiles
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.LocalAdjoint
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingCarrier.Retained
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedKernel

/-!
# Forward data retained with the literal adjoint

`RetainedCellForwardAdjointOutput` is the complete local row endpoint witness.
It keeps the regularized test bounds, reflected amplitude jets, the unique
forward operator, its support and literal adjoint, the strong regularization
limit, the real-quadrature identity, every smaller physical restriction, and
raw Sobolev bounds for that same operator. This is the conclusion proved by
`exists_uniform_retained_cell_carrierAdjoint_full`; the finite retained row
and its initial-variable adjoint consume those joint witnesses
(`app:ch_background:defn:bg-row`, `app:ch_background:eq:bg-T`,
`app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-derivative-trade`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumAdjoint.Canonical.RetainedCellAdjoint
open ContinuumRow DerivativeKernels ModifiedNormalSymbol PhaseExtension AmplitudeProfiles
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open NullTransport ActualFlow FlowAmplitude ProjectedStressFrame CarrierSobolev
open LeadingPrimitive LeadingWave.FullModulation Pseudodifferential RetainedLeading
open ContinuumNormalReduction
open CanonicalConic CanonicalCarrier CommonMeasurement PeriodicLocalL2
open ContinuumNormalReduction.TransportSymbol
open CarrierNormalRealization TransportKernel AmplitudeBound

/-- Complete output of the retained row carrier constructor, including the
literal adjoint at every raw order for the same masks and operator.
The endpoint supplies `H = 1 + cNorm K (s+14) F + cNorm Kinitial (s+14) initial`;
the forward reserve stays fourteen, independently of the raw adjoint reserve
(`app:ch_background:eq:bg-T`, `app:ch_background:prop:bg-adjoint`). -/
def RetainedCellForwardAdjointOutput {n N : ℕ}
    {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {K : Set (Euclidean n)} {Kinitial : Set (Euclidean (n - 1) × Euclidean 3)}
    (z₀ : Euclidean 3) (ηb : Euclidean (n - 1))
    (r a r' a' : ℝ) (ha' : 0 < a')
    (hr' : 0 < r') (hηb : ηb ≠ 0)
    (C Cpdo Cmask H : ℝ) (s : ℕ) (hreserve : 2 * (n + 1) ≤ s)
    (e : CarrierData n N) (d : Coefficients n N)
    (Cbound : ℕ → ℝ) : Prop :=
  let J := symbolJacobian T Q
  let u := symbolInverse T Q z₀ ηb r (6 * a)
  let Ω := symbolDomain T Q z₀ ηb r (6 * a)
  let S := closedBall (spectatorCenter z₀) (a' / 2)
  ∃ hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a',
  ∃ Lmask > 0, ∃ Mmask ≥ 0,
  ∃ hmask : ∀ (R : ℝ), 1 ≤ R → CarrierRegularization.MaskHypotheses e
    (parameterTruncatedMask (carrierSupport z₀ (r := a'))
      (radialCarrierMask FixedCutoffs.radialRegularization R))
    (carrierSupport z₀ (r := a')) (Lmask * R) Mmask Cmask,
    (∀ (R : ℝ) (hR : 1 ≤ R),
      ‖(hmask R hR).operator.comp (hmask R hR).operator.adjoint‖ ≤
          (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H)) ∧
      ‖(realQuadratureChannel (hmask R hR).operator).comp
          (realQuadratureChannel (hmask R hR).operator).adjoint‖ ≤
          (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H))) ∧
    (∀ v : carrierInitialTestSpace n,
      MemLp (carrierTestIntegral e v.val) 2 volume ∧
      (eLpNorm (carrierTestIntegral e v.val) 2 volume).toReal ≤
        Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H))) *
          ‖carrierInitialTestToLp v‖) ∧
  ∃ (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude d J u Ω S)))
    (hA : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude d J u Ω S ξ z i j) s (Cpdo * H)),
  ∃ V : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
    ‖V‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H))) ∧
    ‖V.adjoint‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H))) ∧
    (∀ v : carrierInitialTestSpace n,
      V (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) ∧
    (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → V f x = 0) ∧
    (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ v : carrierInitialTestSpace n,
        W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) → W = V) ∧
    (∀ w : ComplexOutputL2 n,
      MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
      V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) ∧
    (∀ w : ComplexOutputL2 n,
      Filter.Tendsto (fun k : ℕ ↦
        (hmask ((k : ℝ) + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k))).operator.adjoint w)
        Filter.atTop (nhds (V.adjoint w))) ∧
    (realQuadratureChannel V).comp (realQuadratureChannel V).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator (by have := row.isLt; omega) (4 * a')
          (fullReflectedMatrixAmplitude d J u Ω S) hb
          (fullReflectedMatrixAmplitude_supportedInCenteredBox
            d J u Ω S (4 * a') hsupport)
          (Cpdo * H) (fun i j ξ is his ↦ hA i j ξ is (his.trans hreserve)))) ∧
    (∀ {b : ℝ} (hb : 0 < b) (hbcell : 4 * b < 1 / 2), 6 * b < a' →
      let χ := FixedCutoffs.periodic (n := n) hb hbcell 1
      let Vb := CommonMeasurement.restrictCarrier χ V
      let eb := data T Q F row col φ y initial hb hbcell
        (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
        FixedCutoffs.highFrequency
      ‖Vb‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H))) ∧
      (∀ v : carrierInitialTestSpace n,
        Vb (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral eb v.val) ∧
      (∀ w : ComplexOutputL2 n,
        MemLp (carrierAdjointIntegral eb w) 2 (carrierMeasure n) ∧
        Vb.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral eb w) ∧
      (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ eb.outputChart → Vb f x = 0) ∧
      carrierChannel Vb ∘L (carrierChannel Vb).adjoint =
        cutoffMultiplier χ ∘L
          (carrierChannel V ∘L (carrierChannel V).adjoint) ∘L cutoffMultiplier χ) ∧
    ∀ q : ℕ, ∀ v : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) q,
      MemRawSobolev q (V.adjoint (PeriodicSobolevSpace.toL2 q v)) ∧
      rawSobolevNorm q (V.adjoint (PeriodicSobolevSpace.toL2 q v)) ≤
        Cbound q * (‖v‖ + (1 + cNorm K (q + 2 * (n + 1) + 14) F +
          cNorm Kinitial (q + 2 * (n + 1) + 14) initial) *
          ‖PeriodicSobolevSpace.toL2 q v‖)

end JanetCartan.ContinuumAdjoint.Canonical.RetainedCellAdjoint
