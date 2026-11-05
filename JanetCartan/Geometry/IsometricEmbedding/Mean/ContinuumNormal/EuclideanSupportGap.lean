module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.EuclideanSupportGap.Support
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.EuclideanSupportGap.Complexification

/-!
# Euclidean frozen energy on small support

The Euclidean Fourier deduction in `paper-v2.tex`,
`app:ch_background:prop:bg-frame`: a uniformly bounded continuous symbol,
nonnegative everywhere and uniformly positive above a fixed physical frequency,
has a half-gap on a sufficiently small inner physical ball. Plancherel, the
L¹ Fourier bound, integrability, and finite-support Cauchy–Schwarz are proved
from the existing Mathlib L² transform. The explicit loss uses the Lebesgue
volume of the cycles-frequency ball of radius `R₀ / (2π)`.

The image-error allowance and outer cap are fixed before choosing the inner
radius. This is a frozen-energy theorem only. Its consumers, the actual frozen
model and continuum normal, must supply the bounds for their same symbol and
prove both the exact normal-energy identity and the fixed-cutoff image comparison.
The real-matrix adapter transfers real quadratic positivity to complex vectors.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumNormal.EuclideanSupportGap

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℂ (Fin n)
local notation "L²" => Lp (α := E) V 2 volume

/-- The real-matrix endpoint for the actual frozen model in
`app:ch_background:prop:bg-frame`. All positivity premises concern real vectors;
continuity, boundedness and both spectral bounds of the complex multiplier are
derived by the adapter. The parent still owes its literal normal-energy identity
and image comparison with this same matrix symbol and fixed `C_image`. -/
theorem exists_inner_radius_gap_real_matrix (hn : 0 < n)
    (a : E → Matrix (Fin n) (Fin n) ℝ) (ha : Continuous a)
    {c M R₀ C_image : ℝ} (hc : 0 < c) (hC : 0 ≤ C_image)
    (hM : ∀ k, ‖(a k).toEuclideanLin.toContinuousLinearMap‖ ≤ M)
    (hnonneg : ∀ k v, 0 ≤ inner ℝ v ((a k).toEuclideanLin v))
    (hgap : ∀ k, R₀ ≤ ‖k‖ → ∀ v, c * ‖v‖ ^ 2 ≤ inner ℝ v ((a k).toEuclideanLin v))
    {r_outer : ℝ} (houter : 0 < r_outer) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ r_outer ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ u : L²,
        (∀ᵐ x, x ∉ Metric.ball (0 : E) r → u x = 0) →
        c / 2 * ‖u‖ ^ 2 ≤
          energy (fun k ↦ complexifyMatrix (a k)) u - C_image * (∫ x, ‖u x‖) ^ 2 := by
  exact exists_inner_radius_gap hn (fun k ↦ complexifyMatrix (a k))
    (continuous_complexifyMatrix ha) hc hC
    (fun k ↦ norm_complexifyMatrix_le (a k) (hM k))
    (fun k ↦ complexifyMatrix_nonneg (a k) (hnonneg k))
    (fun k hk ↦ complexifyMatrix_gap (a k) (hgap k hk)) houter

end JanetCartan.ContinuumNormal.EuclideanSupportGap
