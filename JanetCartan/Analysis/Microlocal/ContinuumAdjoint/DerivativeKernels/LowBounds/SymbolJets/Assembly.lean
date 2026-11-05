module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.DensityBounds
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.GraphBounds

/-!
# Modified normal bounds from primitive half-order jets

For `app:ch_background:prop:bg-adjoint`, assemble the finite primitive reserve
with buffered extension, differentiation through the compact spectator integral,
and the exact physical-to-cycles normalization. The resulting position jets and
`GraphNormalAmplitudeBounds` have budget `C * A^2`, with `C` chosen before the
arbitrary complex amplitude and smooth regularizer.

The reserve is `N = 2 * (n + 1)` mixed derivatives of the linearly rescaled
original amplitude and regularizer, and of the weighted inverse and original
Jacobian. Producing the Jacobian from the forward map requires order `N + 1`.
The two half-order amplitude weights cancel its degree-one determinant gap.
No estimate on a composed amplitude, inverse density, or operator is an input.

The consumer is the modified carrier L² construction in `LowBounds`. It must
instantiate the primitive geometry and amplitude inputs and supply the actual
regularized normal identity; the present results prove the amplitude bounds.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol

open ContinuumRow FourierIntegral

variable {n : ℕ}

/-- Finite position jets of the actual normalized two-position normal in
`app:ch_background:prop:bg-adjoint`, derived entirely from the primitive
half-order symbol reserve. The constant includes the compact spectator volume,
the exact factor `(2π)^n`, the fixed position inclusion, and the fixed regularizer
budget. The frequency argument of `positionAmplitude` is `η_normal = 2π ξ`.
This is the scalar bound for the modified carrier L² consumer. -/
theorem PrimitiveJetGeometry.exists_positionAmplitude_jet_bound
    {g : Chart n} {s : JetRescaling g} {ρ B c : ℝ}
    {L : Set (JointVariables n)} {K : Set (Euclidean 2)}
    (hg : PrimitiveJetGeometry g s (2 * (n + 1)) ρ B c L K)
    (X : Set (Euclidean n)) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n - 1))) (M : ℝ) :
    ∃ C ≥ 0, ∀ (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (A : ℝ),
      PrimitiveRegularity g a m →
      PrimitiveAmplitudeReserve g (2 * (n + 1)) ρ A X K Z Ω L a →
      PrimitiveRegularizerReserve (2 * (n + 1)) ρ M m →
      ∀ ξ j, j ≤ 2 * (n + 1) → ∀ z,
        ‖iteratedFDeriv ℝ j (positionAmplitude g a m ξ) z‖ ≤ C * A^2 := by
  obtain ⟨D, hD, hd⟩ := hg.exists_inverseDensity_section_jet_bound X Z Ω M
  refine ⟨graphJetFactor n K * D, mul_nonneg (graphJetFactor_nonneg K) hD, ?_⟩
  intro a m A h ha hm ξ j hj z
  simpa only [mul_assoc] using
    norm_iteratedFDeriv_positionAmplitude_le h ha.buffered ha.compact_supports
      (mul_nonneg hD (sq_nonneg A)) (hd a m A h ha hm) ξ j hj z

/-- The actual scalar normal, packaged as a one-by-one matrix, satisfies
`GraphNormalAmplitudeBounds` from primitive half-order jets alone
(`app:ch_background:prop:bg-adjoint`). Its smoothness across chart boundaries,
common measurement support, and finite derivative estimate are all proved.
The constant is uniform over amplitudes of budget `A` and all smooth frequency
regularizations with fixed primitive scaled-derivative budget `M`.
The modified carrier L² consumer supplies only the primitive inputs and a box
containing their fixed measurement support, not density or normal bounds. -/
theorem PrimitiveJetGeometry.exists_graphNormalAmplitudeBounds
    {g : Chart n} {s : JetRescaling g} {ρ B c : ℝ}
    {L : Set (JointVariables n)} {K : Set (Euclidean 2)}
    (hg : PrimitiveJetGeometry g s (2 * (n + 1)) ρ B c L K)
    (X : Set (Euclidean n)) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n - 1))) (M : ℝ)
    {R : ℝ} (hX : ∀ x ∈ X, ∀ i, |x i| ≤ R) :
    ∃ C ≥ 0, ∀ (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (A : ℝ),
      PrimitiveRegularity g a m →
      PrimitiveAmplitudeReserve g (2 * (n + 1)) ρ A X K Z Ω L a →
      PrimitiveRegularizerReserve (2 * (n + 1)) ρ M m →
      GraphNormalAmplitudeBounds (matrixAmplitude g a m) R (C * A^2) := by
  obtain ⟨D, hD, hd⟩ := hg.exists_inverseDensity_section_jet_bound X Z Ω M
  refine ⟨graphJetFactor n K * D, mul_nonneg (graphJetFactor_nonneg K) hD, ?_⟩
  intro a m A h ha hm
  simpa only [mul_assoc] using
    graphNormalAmplitudeBounds_of_densityJets h ha.buffered ha.compact_supports
      (mul_nonneg hD (sq_nonneg A)) hX (hd a m A h ha hm)

/-- Choose the common measurement box and jet constant before the amplitude
and regularization, using only compactness of the primitive measurement set
(`app:ch_background:prop:bg-adjoint`). This discharges the box-containment
premise of `exists_graphNormalAmplitudeBounds` for the modified carrier L²
consumer; every remaining hypothesis is primitive geometry, regularity,
support, or a finite weighted jet budget. -/
theorem PrimitiveJetGeometry.exists_graphNormalAmplitudeBounds_of_isCompact
    {g : Chart n} {s : JetRescaling g} {ρ B c : ℝ}
    {L : Set (JointVariables n)} {K : Set (Euclidean 2)}
    (hg : PrimitiveJetGeometry g s (2 * (n + 1)) ρ B c L K)
    {X : Set (Euclidean n)} (hX : IsCompact X) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n - 1))) (M : ℝ) :
    ∃ R ≥ 0, ∃ C ≥ 0,
      ∀ (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (A : ℝ),
      PrimitiveRegularity g a m →
      PrimitiveAmplitudeReserve g (2 * (n + 1)) ρ A X K Z Ω L a →
      PrimitiveRegularizerReserve (2 * (n + 1)) ρ M m →
      GraphNormalAmplitudeBounds (matrixAmplitude g a m) R (C * A^2) := by
  obtain ⟨R, hR⟩ := hX.isBounded.exists_norm_le
  refine ⟨max 0 R, le_max_left _ _, ?_⟩
  apply hg.exists_graphNormalAmplitudeBounds X Z Ω M
  intro x hx i
  have hi : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  exact hi.trans ((hR x hx).trans (le_max_right _ _))

end JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol
