module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenCoercivity.ImageEnergy

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite frozen row gaps under initial carrier comparisons

For `app:ch_background:prop:bg-frame`, a factor `1/16` comparison of each
real carrier adjoint energy gives the same comparison for the finite physical
row and its augmented normal. The image operator and the cutoff are identical
on both sides. The real channels already contain both quadratures and the
factor four of `app:ch_background:eq:bg-realification`; the exterior normal is
the literal `(1 - ψ)²` of `ContinuumRow.augmentedNormal_eq_sum`.

These are conditional deductions for the final assembly in
`jc-frozen-initial-multiplier-realization`. The channel comparison must be
supplied by `jc-frozen-initial-input-realization`, which constructs `W` by the
literal initial input multiplier. The original local and global gaps are
produced by `FrozenCoercivity.exists_finite_realized_frozen_row_gap`, with
`c = γ / 2` and `c₀ = NormalAugmentation.globalGap (γ / 2) ‖physicalRow image V‖`.
The last theorem takes those same gap outputs and keeps their radius, cutoff
and exterior core. No construction of `W` or unconditional nonconstant gap
is asserted here.
-/

@[expose] public noncomputable section

open MeasureTheory Metric

namespace JanetCartan.ContinuumNormal.FrozenModel.InitialMultiplier

open ContinuumRow PeriodicLocalL2 FrozenImageComparison AmplitudeBound

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Sum the real carrier adjoint comparisons on the same finite physical row
(`app:ch_background:eq:bg-local-bound`, `app:ch_background:eq:bg-realification`).
The unchanged image energy is nonnegative; both carrier quadratures are already
included. Consumed by `supported_physicalRow_gap_of_initial_comparison` and the
augmented-normal comparison below. -/
theorem physicalRow_adjoint_energy_le_of_initial_comparison
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (V W : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hchannel : ∀ i (w : OutputL2 n),
      (1 / 16 : ℝ) * ‖(realQuadratureChannel (V i)).adjoint w‖ ^ 2 ≤
        ‖(realQuadratureChannel (W i)).adjoint w‖ ^ 2)
    (w : OutputL2 n) :
    (1 / 16 : ℝ) * ‖(physicalRow image V).adjoint w‖ ^ 2 ≤
      ‖(physicalRow image W).adjoint w‖ ^ 2 := by
  rw [FrozenCoercivity.physicalRow_adjoint_norm_sq,
    FrozenCoercivity.physicalRow_adjoint_norm_sq, mul_add, Finset.mul_sum]
  apply add_le_add
  · nlinarith only [sq_nonneg ‖image.adjoint w‖]
  · exact Finset.sum_le_sum fun i _ ↦ hchannel i w

/-- The same cutoff and unchanged exterior energy preserve the factor `1/16`
in quadratic-form order (`app:ch_background:eq:bg-global-bound`). The normal is
the existing `augmentedNormal`, whose exterior term is literally `(1 - ψ)²`.
Consumed by `augmentedNormal_gap_of_initial_comparison`. -/
theorem augmentedNormal_inner_le_of_initial_comparison
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (V W : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hchannel : ∀ i (w : OutputL2 n),
      (1 / 16 : ℝ) * ‖(realQuadratureChannel (V i)).adjoint w‖ ^ 2 ≤
        ‖(realQuadratureChannel (W i)).adjoint w‖ ^ 2)
    (ψ : C(Torus n, ℝ)) (w : OutputL2 n) :
    (1 / 16 : ℝ) * inner ℝ (augmentedNormal image V ψ w) w ≤
      inner ℝ (augmentedNormal image W ψ w) w := by
  have hnormal (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
      inner ℝ (augmentedNormal image T ψ w) w =
        ‖(physicalRow image T).adjoint w‖ ^ 2 + ‖exteriorChannel ψ w‖ ^ 2 := by
    have h := (augmentedRow image T ψ).adjoint.apply_norm_sq_eq_inner_adjoint_left w
    simpa only [ContinuousLinearMap.adjoint_adjoint, RCLike.re_to_real,
      augmentedNormal, ContinuousLinearMap.comp_apply, augmentedRow_adjoint_apply,
      WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd] using h.symm
  rw [hnormal V, hnormal W]
  have h := physicalRow_adjoint_energy_le_of_initial_comparison image V W hchannel w
  nlinarith only [h, sq_nonneg ‖exteriorChannel ψ w‖]

/-- Transfer any positive local gap `c` to `c/16` on the original supported
fields (`app:ch_background:eq:bg-local-bound`). The support radius is unchanged.
Consumed by `frozen_row_gaps_of_initial_comparison`; its original gap is supplied
by `FrozenCoercivity.exists_finite_realized_frozen_row_gap`. -/
theorem supported_physicalRow_gap_of_initial_comparison
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (V W : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hchannel : ∀ i (w : OutputL2 n),
      (1 / 16 : ℝ) * ‖(realQuadratureChannel (V i)).adjoint w‖ ^ 2 ≤
        ‖(realQuadratureChannel (W i)).adjoint w‖ ^ 2)
    {c r : ℝ} (hc : 0 < c)
    (hlocal : ∀ w : OutputL2 n,
      (∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : Euclidean n) r → w z = 0) →
      c * ‖w‖ ^ 2 ≤ ‖(physicalRow image V).adjoint w‖ ^ 2) :
    0 < c / 16 ∧ ∀ w : OutputL2 n,
      (∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : Euclidean n) r → w z = 0) →
      c / 16 * ‖w‖ ^ 2 ≤ ‖(physicalRow image W).adjoint w‖ ^ 2 := by
  refine ⟨by positivity, ?_⟩
  intro w hw
  have h := physicalRow_adjoint_energy_le_of_initial_comparison image V W hchannel w
  linarith only [hlocal w hw, h]

/-- Transfer the original positive augmented gap `c₀` to `c₀/16`, with the same
cutoff (`app:ch_background:eq:bg-global-bound`). This uses the original global
gap directly, without a new localization or a norm estimate for the new row.
Consumed by `frozen_row_gaps_of_initial_comparison`. -/
theorem augmentedNormal_gap_of_initial_comparison
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (V W : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hchannel : ∀ i (w : OutputL2 n),
      (1 / 16 : ℝ) * ‖(realQuadratureChannel (V i)).adjoint w‖ ^ 2 ≤
        ‖(realQuadratureChannel (W i)).adjoint w‖ ^ 2)
    (ψ : C(Torus n, ℝ)) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hglobal : ∀ w : OutputL2 n,
      c₀ * ‖w‖ ^ 2 ≤ inner ℝ (augmentedNormal image V ψ w) w) :
    0 < c₀ / 16 ∧ ∀ w : OutputL2 n,
      c₀ / 16 * ‖w‖ ^ 2 ≤ inner ℝ (augmentedNormal image W ψ w) w := by
  refine ⟨by positivity, ?_⟩
  intro w
  have h := augmentedNormal_inner_le_of_initial_comparison image V W hchannel ψ w
  linarith only [hglobal w, h]

/-- Apply the finite-row transfer to the exact local and global constants of
`FrozenCoercivity.exists_finite_realized_frozen_row_gap`
(`app:ch_background:prop:bg-frame`, `app:ch_background:eq:bg-local-bound`,
`app:ch_background:eq:bg-global-bound`). The same radius and inner cutoff give
both positive transferred gaps and the unchanged exterior vanishing on the
core. In particular, the global constant uses the original `V` row norm.
The consumer `jc-frozen-initial-multiplier-realization` must instantiate `W` and
`hchannel` using the actual input-multiplier construction. -/
theorem frozen_row_gaps_of_initial_comparison
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (V W : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hchannel : ∀ i (w : OutputL2 n),
      (1 / 16 : ℝ) * ‖(realQuadratureChannel (V i)).adjoint w‖ ^ 2 ≤
        ‖(realQuadratureChannel (W i)).adjoint w‖ ^ 2)
    {γ r : ℝ} (hγ : 0 < γ) (hr : 0 < r) (hrcell : r < 1 / 2)
    (hlocal : ∀ w : OutputL2 n,
      (∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : Euclidean n) r → w z = 0) →
      γ / 2 * ‖w‖ ^ 2 ≤ ‖(physicalRow image V).adjoint w‖ ^ 2)
    (hglobal : ∀ w : OutputL2 n,
      NormalAugmentation.globalGap (γ / 2) ‖physicalRow image V‖ * ‖w‖ ^ 2 ≤
        inner ℝ (augmentedNormal image V (innerCutoff hr hrcell) w) w) :
    0 < (γ / 2) / 16 ∧
    (∀ w : OutputL2 n,
      (∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : Euclidean n) r → w z = 0) →
      (γ / 2) / 16 * ‖w‖ ^ 2 ≤ ‖(physicalRow image W).adjoint w‖ ^ 2) ∧
    0 < NormalAugmentation.globalGap (γ / 2) ‖physicalRow image V‖ / 16 ∧
    (∀ w : OutputL2 n,
      NormalAugmentation.globalGap (γ / 2) ‖physicalRow image V‖ / 16 * ‖w‖ ^ 2 ≤
        inner ℝ (augmentedNormal image W (innerCutoff hr hrcell) w) w) ∧
    (∀ w : OutputL2 n, ∀ᵐ z ∂volume,
      centeredTorusRepresentative z ∈ closedBall 0 (r / 2) →
        exteriorChannel (innerCutoff hr hrcell) w z = 0) := by
  obtain ⟨hc, hlocal'⟩ := supported_physicalRow_gap_of_initial_comparison
    image V W hchannel (half_pos hγ) hlocal
  obtain ⟨hc₀, hglobal'⟩ := augmentedNormal_gap_of_initial_comparison
    image V W hchannel (innerCutoff hr hrcell)
    (NormalAugmentation.globalGap_pos (half_pos hγ)) hglobal
  exact ⟨hc, hlocal', hc₀, hglobal', inner_exterior_zero_on_core hr hrcell⟩

end JanetCartan.ContinuumNormal.FrozenModel.InitialMultiplier
