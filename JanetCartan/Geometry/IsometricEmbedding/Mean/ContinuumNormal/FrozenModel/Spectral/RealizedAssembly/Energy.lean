module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.EnergyBound.Identification
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.ImageSymbol

/-!
# Fourier energy of the finite frozen sum

The final same-family assembly uses this identity to combine the constructed
carrier energies with the image term. Integrability is derived from the
continuous bounded symbols; the totalized integral is never distributed without
that check (`app:ch_background:prop:bg-frame`, frozen Plancherel step).
-/

@[expose] public noncomputable section
open MeasureTheory Matrix FourierTransform
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel

/-- Combine the actual finite carrier energies and image contribution, keeping
both Fourier quadratures and physical frequency `2πξ`. Consumer:
`exists_finite_realized_frozen_spectral_gap`
(`app:ch_background:prop:bg-frame`). -/
theorem euclideanFrozenEnergy_image_add_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (Q₀ : Fin n → MetricTensor n)
    (b : ι → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hb : ∀ i, Continuous (b i)) (M : ι → ℝ) (hM : ∀ i k, ‖b i k‖ ≤ M i)
    (f : Euclidean n → EuclideanSpace ℂ (Fin n))
    (hf : Integrable f) (hf₂ : MemLp f 2 volume) :
    euclideanFrozenEnergy (fun k ↦ frozenImageSymbol Q₀ k + ∑ i, b i k) f =
      euclideanFrozenEnergy (frozenImageSymbol Q₀) f + ∑ i, euclideanFrozenEnergy (b i) f := by
  classical
  have hi := integrable_euclideanFrozenEnergy_density (frozenImageSymbol Q₀)
    (frozenImageSymbol_continuous Q₀) (frozenImageSymbol_norm_le Q₀) f hf hf₂
  have hc (i : ι) := integrable_euclideanFrozenEnergy_density (b i) (hb i) (hM i) f hf hf₂
  have hquad (a : Matrix (Fin n) (Fin n) ℝ) (c : ι → Matrix (Fin n) (Fin n) ℝ)
      (z : EuclideanSpace ℂ (Fin n)) :
      realifiedMatrixQuadraticForm (a + ∑ i, c i) z =
        realifiedMatrixQuadraticForm a z + ∑ i, realifiedMatrixQuadraticForm (c i) z := by
    simp only [realifiedMatrixQuadraticForm, add_mulVec, sum_mulVec, dotProduct_add,
      dotProduct_sum, Finset.sum_add_distrib]
    ring
  simp only [euclideanFrozenEnergy, hquad]
  rw [integral_add hi (integrable_finsetSum _ (fun i _ ↦ hc i)),
    integral_finsetSum _ (fun i _ ↦ hc i)]

end JanetCartan.ContinuumNormal.FrozenModel
