module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.Coercivity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedLabels
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.InitialMultiplier.FiniteGap

/-!
# The frozen seed conclusion retained by the initialized construction

This is only the spelling of the conclusion of
`exists_initialized_retained_frozen_row`, factored out to keep its large
initializer statement tractable. It is never an input assumption to that
construction. The proof constructs every carrier, multiplier and gap from the
same retained geometry, image comparison and spectral theorem. Both quadratures,
the original exterior square and the full density interval are explicit.
Sources: `app:ch_background:prop:bg-frame`, `bg-local-bound`, `bg-global-bound`.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CommonMeasurement
open FrozenModel InitialMultiplier FrozenCoercivity FrozenImageComparison
open ContinuumNormalReduction CarrierNormalRealization AmplitudeBound ProjectedStressFrame

/-- The actual unit and square-root-density frozen row on supplied initialized
masks and leading cells. This is a constructed conclusion, not a coercivity
premise (`app:ch_background:prop:bg-frame`). -/
def InitializedFrozenSeedGap {n : ℕ} {ι : Type*} [Fintype ι]
    {P : ι → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : ∀ i, PatchQuantitativeFamily (P i) U hU)
    (Q : ∀ i, {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T i).family.threshold})
    (F : Euclidean n → Euclidean (embeddingDimension n)) (row col : ι → Fin n)
    (φ y : ι → ℝ × (Euclidean (n-1) × Euclidean 3) → Euclidean (n-1) × Euclidean 3)
    (z : ι → Euclidean 3) (ηb : ι → Euclidean (n-1)) (r' a' : ι → ℝ)
    (hr' : ∀ i, 0 < r' i) (ha' : ∀ i, 0 < a' i) (hcell' : ∀ i, 4 * a' i < 1 / 2)
    (hηb : ∀ i, ηb i ≠ 0) (zc : ι → Euclidean 3) (L : ι → ℝ) : Prop :=
    let e := fun i ↦ normalizedCarrierData (T i)
      (Q i) F (row i) (col i) (φ i) (y i) (fun _ ↦ 1)
      (ha' i) (hcell' i)
      (angularMask (z i) (NormedSpace.normalize (ηb i))
        (ha' i) (angularWidth_spec (hηb i) (hr' i)).1) FixedCutoffs.highFrequency 0
    ∃ γ > (0 : ℝ), ∃ V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ i v, V i (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral (e i) v.val) ∧
      (∀ i (w : ComplexOutputL2 n), MemLp (carrierAdjointIntegral (e i) w) 2 (carrierMeasure n) ∧
        (V i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
      ∀ (μ : ℝ) (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2), (∀ i, 6 * μ < a' i) →
        let W := fun i ↦ restrictCarrier (FixedCutoffs.periodic hμ hμcell 1) (V i)
        let image := fixedPeriodicChannel hμ hμcell (frozenImageArrays (projectedStress F 0))
        ∃ (rInner : ℝ) (hrInner : 0 < rInner) (hInnerCell : rInner < 1 / 2), rInner ≤ μ ∧
          (∀ w : OutputL2 n,
            (∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w z = 0) →
            γ / 2 * ‖w‖ ^ 2 ≤ ‖(physicalRow image W).adjoint w‖ ^ 2) ∧
          0 < NormalAugmentation.globalGap (γ / 2) ‖physicalRow image W‖ ∧
          (∀ w : OutputL2 n,
            NormalAugmentation.globalGap (γ / 2) ‖physicalRow image W‖ * ‖w‖ ^ 2 ≤
              inner ℝ (augmentedNormal image W (innerCutoff hrInner hInnerCell) w) w) ∧
          (∀ w : OutputL2 n, ∀ᵐ z ∂volume,
            centeredTorusRepresentative z ∈ closedBall 0 (rInner / 2) →
              exteriorChannel (innerCutoff hrInner hInnerCell) w z = 0) ∧
          ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
            (∀ i, ContDiffOn ℝ ∞ (v i)
              (ball ((0 : Euclidean (n-1)), zc i) (L i / 4))) →
            (∀ i q, q ∈ closedBall ((0 : Euclidean (n-1)), zc i) (L i / 8) → 1 + v i q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
          ∃ β : ι → CarrierParameter → ℝ,
          ∃ (hβ : ∀ i, ContDiff ℝ ∞ (β i)) (hβBound : ∀ i z, ‖β i z‖ ≤ 4),
            let M := fun i ↦ labelMultiplier (n := n) (β i) (hβ i).continuous (hβBound i)
            let Vinitial := fun i ↦ V i ∘L M i
            let Winitial := fun i ↦ restrictCarrier (FixedCutoffs.periodic hμ hμcell 1) (Vinitial i)
            (∀ i,
              EqOn (β i) (labelWeight (y i) (fun q ↦ Real.sqrt (1 + v i q)))
                (carrierSupport (z i) (r := a' i)) ∧
              (∀ z' ∈ carrierSupport (z i) (r := a' i),
                labelWeight (y i) (fun q ↦ Real.sqrt (1 + v i q)) z' =
                  1 + v i (0, parameter z')) ∧
              ‖M i‖ ≤ 4 ∧ (M i).adjoint = M i ∧
              let ei := normalizedCarrierData (T i) (Q i) F (row i) (col i) (φ i) (y i)
                (fun q ↦ Real.sqrt (1 + v i q)) (ha' i) (hcell' i)
                (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i)
                  (angularWidth_spec (hηb i) (hr' i)).1) FixedCutoffs.highFrequency 0
              (∀ f : carrierInitialTestSpace n,
                Vinitial i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral ei f.val) ∧
              (∀ w : ComplexOutputL2 n, MemLp (carrierAdjointIntegral ei w) 2 (carrierMeasure n) ∧
                (Vinitial i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral ei w) ∧
              Vinitial i ∘L (Vinitial i).adjoint = V i ∘L (M i ∘L M i) ∘L (V i).adjoint ∧
              realQuadratureChannel (Vinitial i) ∘L (realQuadratureChannel (Vinitial i)).adjoint =
                (4 : ℝ) • realOutputCompression (V i ∘L (M i ∘L M i) ∘L (V i).adjoint)) ∧
            (∀ w : OutputL2 n,
              (∀ᵐ z' ∂volume, z' ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w z' = 0) →
              (γ / 2) / 16 * ‖w‖ ^ 2 ≤ ‖(physicalRow image Winitial).adjoint w‖ ^ 2) ∧
            (∀ w : OutputL2 n,
              NormalAugmentation.globalGap (γ / 2) ‖physicalRow image W‖ / 16 * ‖w‖ ^ 2 ≤
                inner ℝ (augmentedNormal image Winitial (innerCutoff hrInner hInnerCell) w) w)

end JanetCartan.ContinuumNormal.RetainedFrozen
