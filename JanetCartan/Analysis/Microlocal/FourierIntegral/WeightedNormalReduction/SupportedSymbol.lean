module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WeightedNormalReduction.Basic
public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.WeightedConstruction

/-!
# The same supported weighted symbol in the diagonal reduction

The uncut-normal symbol and the native-coordinate amplitude in the Taylor
formula agree literally. The original physical carrier supplies the source
plateau, and the supported weighted diagonal retains both the inverse-chart
indicator and the source cutoff. No gap outside the supported chart is used.
Source: `app:ch_regular_base:eq:actual-normal-amplitude` and
`app:ch_regular_base:eq:actual-pdo-remainder`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.WeightedNormalReduction

open AmplitudeBound NormalComparison LowBounds UncutNormal WholeImageGeometry

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Pairing the native Taylor input recovers exactly the uncut-normal symbol,
with its zero extension and physical-to-cycle conversion unchanged. Consumer:
the bounded diagonal reduction in `app:ch_regular_base:eq:actual-pdo-remainder`. -/
theorem pairedNormalAmplitude_cycleCrossNormalAmplitude
    (D : Set E) (S : E → E → ℝ) (A B : E → E → Mat)
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E) :
    pairedNormalAmplitude (fun q ↦ cycleCrossNormalAmplitude D S A B η J q.1 q.2.1 q.2.2) =
      cycleCrossNormalSymbol D S A B η J := by
  funext ξ z
  rw [← pairedPosition_normalPositions z]
  simp

/-- The source plateau of the transformed symbol follows from the original
right-amplitude carrier and the fixed cutoff. No transformed support premise
is needed. Consumer: the exact bounded reduction, for
`app:ch_regular_base:eq:actual-pdo-remainder`. -/
theorem cycleCrossNormalAmplitude_source_plateau
    (D K : Set E) (S : E → E → ℝ) (A B : E → E → Mat)
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
    (β : E → ℝ) (hB : ∀ y u, y ∉ K → B y u = 0)
    (hβ : ∀ y ∈ K, β y = 1) (x y ξ : E)
    (hc : cycleCrossNormalAmplitude D S A B η J x y ξ ≠ 0) : β y = 1 := by
  apply hβ y
  by_contra hy
  apply hc
  simp [cycleCrossNormalAmplitude, extendedCrossNormalAmplitude,
    crossNormalAmplitude, crossNormalNumerator, hB y _ hy, Set.indicator]

/-- The principal amplitude of the actual weighted normal, retaining its
supported diagonal and the independent source cutoff. The only determinant
gaps occur on `X × X × D` and `X × D`, exactly as in the uncut construction.
Consumer: the `P_diagonal_beta` term of
`app:ch_regular_base:eq:actual-pdo-remainder`. -/
theorem weighted_diagonalSymbol_eq_supported_mask_square
    {X D : Set E} {S : E → E → ℝ} (c : E → E → ℝ) (U : E → E → Mat)
    (β : E → ℝ) (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hs : tsupport (Function.uncurry c) ⊆ X ×ˢ D)
    {δ δU : ℝ} (hδ : 0 < δ) (hδU : 0 < δU)
    (hgap : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|)
    (hdet : ∀ x ∈ X, ∀ u ∈ D, δU ≤ ‖(U x u).det‖) (x y ξ : E) :
    diagonalSymbol
      (cycleCrossNormalAmplitude D S (maskedTransportAmplitude c U) (maskedWeightedAmplitude S c U)
        (wholeImageInverse S D) (averagedJacobian S)) β ξ (pairedPosition x y) =
      β y • {v : E | x ∈ X ∧ (2 * Real.pi) • v ∈ averagedGradient S x x '' D}.indicator
        (fun v ↦ (c x (wholeImageInverse S D x x ((2 * Real.pi) • v)) : ℂ)^2 •
          (1 : Mat)) ξ := by
  rw [diagonalSymbol_pairedPosition, ← cycleCrossNormalSymbol_pairedPosition]
  rw [maskedWeighted_cycleSymbol_diagonal_of_primitive_phase c U hX hD hcX hS hs
    hδ hδU hgap hdet]

end JanetCartan.FourierIntegral.WeightedNormalReduction
