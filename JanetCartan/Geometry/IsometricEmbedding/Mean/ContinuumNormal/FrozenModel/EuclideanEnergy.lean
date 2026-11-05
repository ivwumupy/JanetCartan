module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Symbol
public import JanetCartan.Analysis.Microlocal.Localization.PhysicalPlancherel

/-!
# Shared Euclidean frozen-energy expression

The Lebesgue-frequency energy in the frozen step of
`app:ch_background:prop:bg-frame`. Both real Fourier components are included,
and the matrix is evaluated at physical frequency `k = 2πξ`. The carrier
identification and low-frequency estimate consume this same expression.
No identity with a carrier operator, convergence or spectral gap is asserted
by these definitions.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Matrix
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.FrozenModel

variable {n : ℕ}

/-- The sum of the real and imaginary quadratic forms, as required for a
real symmetric multiplier acting on Fourier transforms of real fields
(`app:ch_background:prop:bg-frame`, frozen step). -/
def realifiedMatrixQuadraticForm (M : Matrix (Fin n) (Fin n) ℝ)
    (z : EuclideanSpace ℂ (Fin n)) : ℝ :=
  (fun i ↦ (z i).re) ⬝ᵥ (M *ᵥ (fun i ↦ (z i).re)) +
    (fun i ↦ (z i).im) ⬝ᵥ (M *ᵥ (fun i ↦ (z i).im))

/-- A positive real matrix is positive on both Fourier components
(`app:ch_background:prop:bg-frame`). -/
theorem realifiedMatrixQuadraticForm_nonneg {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) (z : EuclideanSpace ℂ (Fin n)) :
    0 ≤ realifiedMatrixQuadraticForm M z := by
  exact add_nonneg (by simpa using hM.dotProduct_mulVec_nonneg (fun i ↦ (z i).re))
    (by simpa using hM.dotProduct_mulVec_nonneg (fun i ↦ (z i).im))

/-- The actual Euclidean-frequency integral, in Mathlib's unit-frequency
Fourier normalization. Physical symbols are evaluated at `2πξ`; the measure
is Lebesgue volume on all of Euclidean frequency space
(`app:ch_background:prop:bg-frame`, frozen step). -/
def euclideanFrozenEnergy (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (f : Euclidean n → EuclideanSpace ℂ (Fin n)) : ℝ :=
  ∫ ξ, realifiedMatrixQuadraticForm (b ((2 * Real.pi) • ξ)) (𝓕 f ξ)

/-- Nonnegativity of the Euclidean frozen energy follows from pointwise
matrix positivity. Integrability and the carrier identification still have
to be proved separately (`app:ch_background:prop:bg-frame`). -/
theorem euclideanFrozenEnergy_nonneg (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hb : ∀ k, (b k).PosSemidef) (f : Euclidean n → EuclideanSpace ℂ (Fin n)) :
    0 ≤ euclideanFrozenEnergy b f :=
  integral_nonneg fun ξ ↦ realifiedMatrixQuadraticForm_nonneg (hb _) (𝓕 f ξ)

end JanetCartan.ContinuumNormal.FrozenModel
