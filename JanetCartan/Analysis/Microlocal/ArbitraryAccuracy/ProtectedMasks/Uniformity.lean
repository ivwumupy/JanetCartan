module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.FinalMask
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ReachableBounds
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Shoulders
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Masks
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Localization
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicLocalization
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.SupportedGaps
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Construction

/-!
# Coefficient-uniform protected-mask deductions

The common final physical mask is constructed before the current field, roots,
flows, and requested accuracy. Its primitive inputs are the fixed section and
transverse/root bounds of `UniformGeometry/Construction`, a compact physical
envelope, and the SAME comparison geometry and source cover retained by
`ProtectedFlow.exists_initialized_signed_no_return`. The actual finite-family
selector restricts those producer estimates to its initial and segment buffers.

`exists_uniform_nested_physicalDirectLocalizers` now constructs every finite
depth of intermediate physical masks with common support and plateau shoulders,
an annulus, base bounds and all-order derivative constants before the current
field. Their literal canonical pullbacks retain the same constants. The larger
unit-amplitude whole-segment relation is also buffered, without changing the
actual physical factors; this provides room for quantitative stationary tests.

`exists_uniform_nested_localization_data` instantiates those mask margins in
the uniform local interior gap and a common finite-family conic boundary
collar. Its smooth scalar cutoff has global all-order derivative bounds.
The phase budget is extracted from the literal root-flow order-two sum using
the original C³ coefficient bound, restricted to each original physical domain.
`phaseGradientSquare_normalized_extension_eq` transports both squared gradients
to the constructed supported extension on its full radially invariant domain.

`exists_uniform_conic_nested_localization_data` completes the deduction on
the entire fixed conic radial band. A finite radial proof refinement of the
SAME homogeneous root, flow and inverse chart constructs one mask family.
Its whole-segment margin gives the full interior gap, and its full diagonal
margin supplies the boundary collar for the original conic phase. Both gaps
also hold for a constructed continuous homogeneous extension, smooth away
from zero transverse frequency. No extension germ is assumed. The actual
physical factors, both orientations, closed shoulders, output complement,
source recutting and original elapsed interval are retained.

The arbitrary-accuracy consumer retains selection of the actual finite
characteristic and comparison charts, and their fixed domain restrictions.
The uniform deduction assumes only the displayed primitive outputs of those
producers; masks, radial refinements, gap constants and collars are conclusions.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic ActualCarriers HamiltonPhase ProtectedFlow PhaseCover
open FiniteChain.Graph

variable {d : ℕ}

/-- One common final physical mask for every actual finite chain, including
depth zero and elliptic identities, with a positive shoulder, a positive
annulus, and an all-order derivative sequence fixed BEFORE the current field.
No compact coefficient class, successful mask, chain-image hypothesis, or
derivative gap is assumed. Angular protection is derived from the SAME retained
comparison charts and source cover; frequency bounds come from the primitive
section estimates. The original factor masks, both orientations, whole
segments and elapsed interval are retained
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:thm:no-return`).

This is the final-mask part of the construction. Uniform nesting of the
intermediate masks and the quantitative localization gaps remain separate. -/
theorem exists_uniform_final_physicalDirectLocalizer {I J : Type*} [Finite J]
    (ℓ : J → Euclidean d →L[ℝ] ℝ) (η₀ : J → Euclidean d)
    (εroot G : J → ℝ) (hG : ∀ j, 0 ≤ G j)
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hS : IsCompact S) (hSnonzero : ∀ p ∈ S, p.2 ≠ 0)
    {B Γ : Set (Euclidean (d + 1))} (hB : IsCompact B) (hΓ : IsClosed Γ)
    (hSB : ∀ p ∈ S, p.1 ∈ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : LocalizerSymbol (d + 1)) (δ a b R : ℝ) (H : ℕ → ℝ),
      ContDiff ℝ ∞ m ∧ (∀ p, m p ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport m ∧
      0 < δ ∧ 0 < a ∧ a < b ∧ 0 < R ∧
      tsupport m ⊆ physicalProtectedRegion Γ ∧
      tsupport m ⊆ closedBall 0 R ×ˢ PhysicalShells.frequencyAnnulus a b ∧
      (∀ k, 0 ≤ H k) ∧ (∀ k p, ‖iteratedFDeriv ℝ k m p‖ ≤ H k) ∧
      ∀ (i : J → Fin (d + 1))
        (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (hQ : ContDiff ℝ ∞ Q)
        (h : J → RootState (Euclidean d) → ℝ)
        (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (U K D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
        (χsource χout : J → Euclidean (d + 1) → ℂ) (Δ : ℝ),
        (∀ j v, v ∈ U j ∪ K j →
          v.2.2 ∈ closedBall (η₀ j) (εroot j) ∧
          (1 / 2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
        (∀ j v, v ∈ U j ∪ K j → (coordinateSplit (i j)).symm (v.1, v.2.1) ∈ B) →
        (∀ j, K j ⊆ D j) →
        ∀ (z : J → RootState (Euclidean d)) (Rflow rFlow T : J → ℝ),
        (∀ j, ODE.IsSmoothFlowOn (rootHamiltonField (h j))
          (z j) (Rflow j) (rFlow j) (T j) (Φ j)) →
        (∀ j, 0 < T j) → (∀ j, Δ < T j) →
        (∀ j, U j ⊆ closedBall (z j) (rFlow j)) →
        (∀ j, IsOpen (D j)) → (∀ j, ContDiffOn ℝ ∞ (h j) (D j)) →
        (∀ j, ∀ v ∈ D j, v.2.2 ≠ 0 ∧
          determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
            ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
          fderiv ℝ (determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1))))
            ((coordinateSplit (i j)).symm (h j v, v.2.2))
            ((coordinateSplit (i j)).symm (1, 0)) ≠ 0) →
        ∀ (g : I → ComparisonGeometry (Euclidean (d + 1)))
          (C : (j : I) → ComparisonChart
            (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g j)) (r : ℝ),
        (∀ j, 2 * r < (g j).radius) → W ⊆ ball 0 (2 * r) →
        (∀ p ∈ S, normalizedSymbol Q p = 0 →
          p ∈ positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ) →
        (∀ p ∈ positiveConicLift (ComparisonChart.familyGradient C)
          (ball 0 (2 * r)) univ, closedBall (normalizedCovector p.2) ε ⊆ Γ) →
        (∀ p ∈ S, ∀ q k,
          PositiveConicChain (CompleteCharacteristicSegment
            (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (ball 0 (2 * r)))
            p q k → closedBall (normalizedCovector q.2) ε ⊆ Γ) →
        ∀ n, cthickening δ
          (reachableAt (physicalDirectRelation i h Φ U K W χsource χout Δ) S n) ⊆
            interior {p | m p = 1} := by
  obtain ⟨c, hc, C, _, hcarrier⟩ := exists_uniform_reachableAt_annular_carrier_of_section
    ℓ η₀ εroot G hG hS hSnonzero hSB
  obtain ⟨m, δ, a, b, R, H, hm, hδ, ha, hab, hR, hsupp, hH, hjet, hplateau⟩ :=
    exists_common_protectedAnnularLocalizer (b := C) hB hΓ hc hε
  refine ⟨m, δ, a, b, R, H, hm.smooth, hm.range, hm.compactSupport,
    hδ, ha, hab, hR, hm.support_subset, hsupp, hH, hjet, ?_⟩
  intro i Q hQ h Φ U K D W χsource χout Δ hb hbase hKD z Rflow rFlow T
    hflow hT hΔ hUflow hD hh hroot g C r hradius hWball hcover hbuffer hretained n
  apply hplateau
  intro q hq
  refine ⟨hcarrier i h Φ U K W χsource χout Δ hb hbase n hq, ?_⟩
  obtain ⟨p, hp, hchain⟩ := hq
  have hi : ∀ j v, v ∈ U j → Φ j (v, 0) = v :=
    fun j v hv ↦ (hflow j).initial v (hUflow j hv)
  have hode : ∀ j v, v ∈ U j → ∀ t ∈ Icc 0 Δ,
      HasDerivAt (fun s ↦ Φ j (v, s)) (rootHamiltonField (h j) (Φ j (v, t))) t := by
    intro j v hv t ht
    exact (hflow j).hasDerivAt (hUflow j hv)
      ⟨(neg_neg_of_pos (hT j)).trans_le ht.1, ht.2.trans_lt (hΔ j)⟩
  exact physicalDirectRelation_chain_angular_buffer i hQ h Φ U K D χsource χout Δ
    hKD hi hode hD hh hroot C hradius hcover hbuffer hretained hp
    (physicalDirectRelation_chain_mono_physical_buffer hWball hchain)

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
