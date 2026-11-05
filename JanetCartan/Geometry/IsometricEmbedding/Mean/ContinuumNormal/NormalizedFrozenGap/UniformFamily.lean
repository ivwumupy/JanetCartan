module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedFrozenGap.Normalization
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.SeedGap

/-!
# Scale-uniform use of the constructed frozen seed gap

This is the consumer form of `InitializedFrozenSeedGap`, constructed on the
supplied family by `initializedFrozenSeedGap_of_retained_normalized_family`.
One unit row, local constant, global constant and inner cutoff precede the
source scale and the full positive-density class. The frozen image is written
using the actual dilated reference; its cube-frame identity proves that this
is the same image. The carrier is the literal normalized zero slice with its
bounded initial multiplier, both quadratures, and original Lebesgue measure.

This projection does not prove coercivity of the positive-scale current row.
That comparison remains the input to `PositiveBackground.SourceInverse`
owned by the normal-variation and normal-coercivity constructions.
Sources: `app:ch_background:prop:bg-normalized`, `bg-local-bound`, `bg-global-bound`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedFrozenGap

open RetainedFrozen FrozenModel FrozenModel.InitialMultiplier
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CommonMeasurement
open FrozenCoercivity FrozenImageComparison AmplitudeBound ProjectedStressFrame

/-- The already chosen inner cutoff is literally the fixed source cutoff at
half its support radius. This converts the frozen gap to the cutoff convention
of `PositiveBackground.SourceInverse`, preserving the function and hence its
exterior square (`app:ch_background:defn:bg-row`, `bg-global-bound`). -/
theorem innerCutoff_eq_fixedPeriodic_half {n : ℕ} {r : ℝ}
    (hr : 0 < r) (hcell : r < 1 / 2) (hhalf : 4 * (r / 2) < 1 / 2) :
    innerCutoff (n := n) hr hcell = FixedCutoffs.periodic (half_pos hr) hhalf 0 := by
  ext x
  simp only [innerCutoff_apply, FixedCutoffs.periodic_apply, innerPhysicalCutoff,
    FixedCutoffs.physical, Fin.val_zero, Nat.cast_zero, zero_add, one_mul,
    mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-- The same constructed frozen row works for every source scale and every
original positive density. Its two positive constants and cutoff are selected
before `σ` and `v`. The last inequality has the adjoint-norm form required by
`PositiveBackground.SourceInverse`; positive-scale normal perturbation must
still be supplied on this row (`app:ch_background:prop:bg-normalized`). -/
theorem exists_uniform_source_frozen_gaps
    {n : ℕ} {ι : Type*} [Fintype ι]
    {P : ι → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : ∀ i, PatchQuantitativeFamily (P i) U hU)
    (Q : ∀ i, {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T i).family.threshold})
    (G : FlatReference n) (row col : ι → Fin n)
    (Φ Y : ι → ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z : ι → Euclidean 3) (ηb : ι → Euclidean (n - 1)) (r' a' : ι → ℝ)
    (hr' : ∀ i, 0 < r' i) (ha' : ∀ i, 0 < a' i) (hcell' : ∀ i, 4 * a' i < 1 / 2)
    (hηb : ∀ i, ηb i ≠ 0) (zc : ι → Euclidean 3) (L : ι → ℝ)
    (hgap : InitializedFrozenSeedGap T Q G.map row col Φ Y z ηb r' a'
      hr' ha' hcell' hηb zc L)
    {μ : ℝ} (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2) (hμa : ∀ i, 6 * μ < a' i) :
    ∃ cLocal > (0 : ℝ), ∃ cGlobal > (0 : ℝ),
    ∃ V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
    ∃ (rInner : ℝ) (hrInner : 0 < rInner) (hInnerCell : rInner < 1 / 2)
      (hSourceCell : 4 * (rInner / 2) < 1 / 2),
      rInner ≤ μ ∧
      innerCutoff (n := n) hrInner hInnerCell =
        FixedCutoffs.periodic (half_pos hrInner) hSourceCell 0 ∧
      (∀ w : OutputL2 n, ∀ᵐ x ∂volume,
        centeredTorusRepresentative x ∈ closedBall 0 (rInner / 2) →
          exteriorChannel (innerCutoff hrInner hInnerCell) w x = 0) ∧
      ∀ σ : ℝ, 0 < σ → ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
        (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), zc i) (L i / 4))) →
        (∀ i q, q ∈ closedBall ((0 : Euclidean (n - 1)), zc i) (L i / 8) →
          1 + v i q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      ∃ (β : ι → CarrierParameter → ℝ) (hβ : ∀ i, ContDiff ℝ ∞ (β i))
        (hβBound : ∀ i x, ‖β i x‖ ≤ 4),
        let M := fun i ↦ labelMultiplier (n := n) (β i) (hβ i).continuous (hβBound i)
        let Vinitial := fun i ↦ V i ∘L M i
        let W := fun i ↦ restrictCarrier (FixedCutoffs.periodic hμ hμcell 1) (Vinitial i)
        let image := fixedPeriodicChannel hμ hμcell
          (frozenImageArrays (projectedStress (sourceDilation G.map σ) 0))
        (∀ i,
          EqOn (β i) (labelWeight (Y i) (fun q ↦ Real.sqrt (1 + v i q)))
            (carrierSupport (z i) (r := a' i)) ∧
          (∀ x ∈ carrierSupport (z i) (r := a' i),
            labelWeight (Y i) (fun q ↦ Real.sqrt (1 + v i q)) x =
              1 + v i (0, parameter x)) ∧
          ‖M i‖ ≤ 4 ∧ (M i).adjoint = M i ∧
          let ei := normalizedCarrierData (T i) (Q i) G.map (row i) (col i)
            (Φ i) (Y i) (fun q ↦ Real.sqrt (1 + v i q)) (ha' i) (hcell' i)
            (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i)
              (angularWidth_spec (hηb i) (hr' i)).1) FixedCutoffs.highFrequency 0
          (∀ f : carrierInitialTestSpace n,
            Vinitial i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral ei f.val) ∧
          (∀ w : ComplexOutputL2 n,
            MemLp (carrierAdjointIntegral ei w) 2 (carrierMeasure n) ∧
            (Vinitial i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral ei w) ∧
          Vinitial i ∘L (Vinitial i).adjoint = V i ∘L (M i ∘L M i) ∘L (V i).adjoint ∧
          realQuadratureChannel (Vinitial i) ∘L (realQuadratureChannel (Vinitial i)).adjoint =
            (4 : ℝ) • realOutputCompression (V i ∘L (M i ∘L M i) ∘L (V i).adjoint)) ∧
        (∀ w : OutputL2 n,
          (∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) →
          cLocal * ‖w‖ ^ 2 ≤ ‖(physicalRow image W).adjoint w‖ ^ 2) ∧
        (∀ w : OutputL2 n, cGlobal * ‖w‖ ^ 2 ≤
          inner ℝ (augmentedNormal image W (innerCutoff hrInner hInnerCell) w) w) ∧
        (∀ w : OutputL2 n, cGlobal * ‖w‖ ^ 2 ≤
          ‖(augmentedRow image W
            (FixedCutoffs.periodic (half_pos hrInner) hSourceCell 0)).adjoint w‖ ^ 2) := by
  obtain ⟨γ, hγ, V, _htest, _hadj, hgaps⟩ := hgap
  obtain ⟨rInner, hrInner, hInnerCell, hrμ, _hlocal, hglobalPos, _hglobal, hext, hweighted⟩ :=
    hgaps μ hμ hμcell hμa
  have hSourceCell : 4 * (rInner / 2) < 1 / 2 := by linarith
  have hcutoff := innerCutoff_eq_fixedPeriodic_half (n := n) hrInner hInnerCell hSourceCell
  refine ⟨(γ / 2) / 16, by positivity,
    NormalAugmentation.globalGap (γ / 2)
      ‖physicalRow (fixedPeriodicChannel hμ hμcell (frozenImageArrays (projectedStress G.map 0)))
        (fun i ↦ restrictCarrier (FixedCutoffs.periodic hμ hμcell 1) (V i))‖ / 16,
    div_pos hglobalPos (by norm_num), V, rInner, hrInner, hInnerCell, hSourceCell,
    hrμ, hcutoff, hext, ?_⟩
  intro σ hσ v hv hden
  obtain ⟨β, hβ, hβBound, hreal, hlocal, hglobal⟩ := hweighted v hv hden
  have hframe : projectedStress (sourceDilation G.map σ) 0 = projectedStress G.map 0 := by
    rw [projectedStress_sourceDilation_origin G hσ]
    exact (funext (projectedStress_flatReference_zero G)).symm
  refine ⟨β, hβ, hβBound, hreal, ?_, ?_, ?_⟩
  · simpa only [hframe] using hlocal
  · simpa only [hframe] using hglobal
  · intro w
    have he := (augmentedRow
      (fixedPeriodicChannel hμ hμcell (frozenImageArrays (projectedStress G.map 0)))
      (fun i ↦ restrictCarrier (FixedCutoffs.periodic hμ hμcell 1)
        (V i ∘L labelMultiplier (β i) (hβ i).continuous (hβBound i)))
      (innerCutoff hrInner hInnerCell)).adjoint.apply_norm_sq_eq_inner_adjoint_left w
    simp only [ContinuousLinearMap.adjoint_adjoint, RCLike.re_to_real] at he
    simpa only [hframe, ← hcutoff] using (hglobal w).trans_eq he.symm

end JanetCartan.ContinuumNormal.NormalizedFrozenGap
