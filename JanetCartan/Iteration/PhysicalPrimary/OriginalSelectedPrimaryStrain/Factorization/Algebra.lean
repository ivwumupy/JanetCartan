module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial.Formulas

/-!
# Recombining the original raw primary differential

The original baseline and full annular raw field carry the same undoubled
phase.  These two elementary identities are used by their actual factorization
on the original source chart (`main:eq:primary-strain`).  The observation is
removed only where its existing plateau equals one.
-/

@[expose] public noncomputable section

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization

open RawPrimary.AmplitudeGrades.Polynomial
open scoped Matrix.Norms.Frobenius

/-- Remove the original observation on its one-plateau and undo the ordinary
carrier demodulation.  Neither an angular factor nor a weight is divided. -/
theorem matrix_eq_of_observed_demodulation {n N : ℕ}
    (A D : Matrix (Fin N) (Fin n) ℂ) (θ ψ : ℝ)
    (hψ : ψ = 1)
    (h : ψ • (Complex.exp (-Complex.I * (θ : ℂ)) • A) = D) :
    A = Complex.exp (Complex.I * (θ : ℂ)) • D := by
  rw [hψ, one_smul] at h
  rw [← h, smul_smul, ← Complex.exp_add]
  have hz : Complex.I * (θ : ℂ) + -Complex.I * (θ : ℂ) = 0 := by ring
  rw [hz, Complex.exp_zero, one_smul]

/-- The same carrier factors out of the full baseline-plus-angular derivative.
Its two factorization premises are supplied by the original raw producers. -/
theorem raw_sum_derivative_factor {n N : ℕ}
    (Z W : Euclidean n → EuclideanSpace ℂ (Fin N)) (x : Euclidean n)
    (B D : Matrix (Fin N) (Fin n) ℂ) (θ ψ : ℝ)
    (hZ : DifferentiableAt ℝ Z x) (hW : DifferentiableAt ℝ W x)
    (hψ : ψ = 1)
    (hB : RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N (fderiv ℝ Z x) =
      Complex.exp (Complex.I * (θ : ℂ)) • B)
    (hD : ψ • (Complex.exp (-Complex.I * (θ : ℂ)) •
      RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N (fderiv ℝ W x)) = D) :
    RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N (fderiv ℝ (Z + W) x) =
      Complex.exp (Complex.I * (θ : ℂ)) • (B + D) := by
  rw [fderiv_add hZ hW, map_add, hB,
    matrix_eq_of_observed_demodulation _ _ θ ψ hψ hD, smul_add]

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization
