module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Diagonal
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Basic

/-!
# Weighted diagonal on the supported inverse chart

The forward weighted amplitude in `app:ch_regular_base:eq:actual-matrix-inverse`
is formed from the same real mask as the transport amplitude. The mask may
include both physical and conic cutoffs. The diagonal computation retains its
square, uses the actual whole-image inverse, and requires gaps only on the
supported chart. This supplies the diagonal of the uncut cross-normal to the
coordinate-inverse construction; it does not identify the uncut operators.
-/

@[expose] public noncomputable section

open Set
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.UncutNormal

open NormalComparison LowBounds WholeImageGeometry

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The original transport amplitude with all physical and conic masks kept.
For a pure frequency mask this is `χ_g U` in
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
def maskedTransportAmplitude (c : E → E → ℝ) (U : E → E → Mat) : E → E → Mat :=
  fun x u ↦ (c x u : ℂ) • U x u

/-- The forward amplitude whose literal adjoint is the manuscript's weighted
reverse graph: `c j_S U⁻*`. The original mask is unchanged. Source:
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
def maskedWeightedAmplitude (S : E → E → ℝ) (c : E → E → ℝ)
    (U : E → E → Mat) : E → E → Mat :=
  fun x u ↦ (c x u : ℂ) • weightedForwardAmplitude (phaseJacobian S x u) (U x u)

/-- The literal adjoint weight retains the complete real mask, for
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem maskedWeightedAmplitude_conjTranspose (S : E → E → ℝ)
    (c : E → E → ℝ) (U : E → E → Mat) (x u : E) :
    (maskedWeightedAmplitude S c U x u).conjTranspose =
      (c x u : ℂ) • reverseWeight (phaseJacobian S x u) (U x u) := by
  simp only [maskedWeightedAmplitude, Matrix.conjTranspose_smul,
    weightedForwardAmplitude_conjTranspose, Complex.star_def, Complex.conj_ofReal]

/-- Weighted cancellation on an arbitrary supported inverse-chart diagonal.
No derivative or inverse gap is needed where the mask vanishes. Consumer:
the diagonal of the pure cross-normal in
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem maskedWeighted_crossNormalAmplitude_diagonal
    (S : E → E → ℝ) (c : E → E → ℝ) (U : E → E → Mat)
    (η : E → E → E → E) (x ξ : E)
    (hgrad : c x (η x x ξ) ≠ 0 →
      DifferentiableAt ℝ (fun u ↦ gradient (fun z ↦ S z u) x) (η x x ξ))
    (hgap : c x (η x x ξ) ≠ 0 → phaseJacobian S x (η x x ξ) ≠ 0)
    (hU : c x (η x x ξ) ≠ 0 → IsUnit (U x (η x x ξ)).det) :
    crossNormalAmplitude (maskedTransportAmplitude c U) (maskedWeightedAmplitude S c U)
      η (averagedJacobian S) x x ξ =
        (c x (η x x ξ) : ℂ)^2 • (1 : Mat) := by
  by_cases hc : c x (η x x ξ) = 0
  · simp [crossNormalAmplitude, crossNormalNumerator, maskedTransportAmplitude,
      maskedWeightedAmplitude, hc]
  · unfold crossNormalAmplitude crossNormalNumerator
    rw [averagedJacobian, averagedGradient_diagonal_det S x (η x x ξ) (hgrad hc)]
    exact weighted_cutoff_principal_amplitude _ _ (hgap hc) _ (hU hc)

/-- The diagonal of the literal buffered zero extension in cycle frequency.
The Jacobian gap is the original averaged-gradient gap on the chart, and the
matrix is invertible only where the original mask is nonzero. Off the chart
both sides vanish. Thus this identity imposes no global phase invertibility.
Source: `app:ch_regular_base:eq:actual-normal-amplitude` and
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem maskedWeighted_extended_diagonal
    (X D : Set E) (S : E → E → ℝ) (c : E → E → ℝ) (U : E → E → Mat)
    {δ : ℝ} (hδ : 0 < δ)
    (hgrad : ∀ x ∈ X, ∀ u ∈ D, c x u ≠ 0 →
      DifferentiableAt ℝ (fun v ↦ gradient (fun z ↦ S z v) x) u)
    (hgap : ∀ x ∈ X, ∀ u ∈ D, c x u ≠ 0 → δ ≤ |(averagedJacobian S x x u).det|)
    (hU : ∀ x ∈ X, ∀ u ∈ D, c x u ≠ 0 → IsUnit (U x u).det)
    (x ξ : E) :
    extendedCrossNormalAmplitude (bufferedNormalDomain X D S)
      (maskedTransportAmplitude c U) (maskedWeightedAmplitude S c U)
      (wholeImageInverse S D) (averagedJacobian S) (x, x, (2 * Real.pi) • ξ) =
      {v : E | x ∈ X ∧ (2 * Real.pi) • v ∈ averagedGradient S x x '' D}.indicator
        (fun v ↦ (c x (wholeImageInverse S D x x ((2 * Real.pi) • v)) : ℂ)^2 •
          (1 : Mat)) ξ := by
  classical
  by_cases h : x ∈ X ∧ (2 * Real.pi) • ξ ∈ averagedGradient S x x '' D
  · have hΩ : (x, x, (2 * Real.pi) • ξ) ∈ bufferedNormalDomain X D S :=
      ⟨h.1, h.1, h.2⟩
    have hu := wholeImageInverse_mem h.2
    rw [extendedCrossNormalAmplitude, indicator_of_mem hΩ,
      indicator_of_mem (show ξ ∈ {v : E | x ∈ X ∧
        (2 * Real.pi) • v ∈ averagedGradient S x x '' D} from h)]
    apply maskedWeighted_crossNormalAmplitude_diagonal
    · exact hgrad x h.1 _ hu
    · intro hc
      have hg := hδ.trans_le (hgap x h.1 _ hu hc)
      rw [averagedJacobian, averagedGradient_diagonal_det S x _ (hgrad x h.1 _ hu hc)] at hg
      exact ne_of_gt hg
    · exact hU x h.1 _ hu
  · have hΩ : (x, x, (2 * Real.pi) • ξ) ∉ bufferedNormalDomain X D S :=
      fun hh ↦ h ⟨hh.1, hh.2.2⟩
    rw [extendedCrossNormalAmplitude, indicator_of_notMem hΩ,
      indicator_of_notMem (show ξ ∉ {v : E | x ∈ X ∧
        (2 * Real.pi) • v ∈ averagedGradient S x x '' D} from h)]

end JanetCartan.FourierIntegral.UncutNormal
