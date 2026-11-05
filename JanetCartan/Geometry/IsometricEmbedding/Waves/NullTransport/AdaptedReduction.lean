module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.Reduction

/-!
# Reduction in the actual adapted time direction

The section normal retained by the carrier construction need not be a standard
coordinate vector. These identities use that literal normal without rotating the
projected stress frame (`app:ch_waves:thm:leading`). The consumer is the positive
transport construction on the same carrier chart.
-/

@[expose] public noncomputable section
open scoped Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NullTransport

variable {n N : ℕ}

/-- The coefficient of the actual adapted time variable `t = ⟪ν,x⟫`
in `app:ch_waves:thm:leading`. -/
def adaptedTimeCoefficient (Q : Fin n → MetricTensor n) (ξ : Euclidean n)
    (r c : Fin n) (ν : Euclidean n) : ℝ :=
  ∑ a, ν a * transportField Q (leftNullvector (reducedSymbol Q ξ) r)
    (rightNullvector (reducedSymbol Q ξ) c) a

/-- The adapted time coefficient is the selected minor times the determinant
differential in the actual section normal (`app:ch_waves:thm:leading`). -/
theorem adaptedTimeCoefficient_eq_minor_mul_fderiv
    (Q : Fin n → MetricTensor n) (hQ : ∀ i, (Q i).IsSymm) (ξ : Euclidean n)
    (hchar : reducedDeterminant Q ξ = 0) {r c : Fin n}
    (hminor : (reducedSymbol Q ξ).adjugate r c ≠ 0) (ν : Euclidean n) :
    adaptedTimeCoefficient Q ξ r c ν =
      (reducedSymbol Q ξ).adjugate r c * fderiv ℝ (reducedDeterminant Q) ξ ν := by
  have hs : (∑ a, ν a * partialDeriv (reducedDeterminant Q) ξ a) =
      fderiv ℝ (reducedDeterminant Q) ξ ν := by
    simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply, partialDeriv, smul_eq_mul] using
      congrArg (fderiv ℝ (reducedDeterminant Q) ξ)
        ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr ν)
  simp only [adaptedTimeCoefficient,
    transportField_eq_minor_mul_partialDeriv Q hQ ξ hchar hminor]
  simp_rw [mul_left_comm (ν _) ((reducedSymbol Q ξ).adjugate r c),
    ← Finset.mul_sum, hs]

/-- Fixed minor and adapted root gaps bound the actual time denominator and
its reciprocal (`app:ch_waves:thm:leading`). -/
theorem adaptedTimeCoefficient_bounds
    (Q : Fin n → MetricTensor n) (hQ : ∀ i, (Q i).IsSymm) (ξ : Euclidean n)
    (hchar : reducedDeterminant Q ξ = 0) {r c : Fin n} (ν : Euclidean n)
    {μ κ : ℝ} (hμ : 0 < μ) (hκ : 0 < κ)
    (hminor : μ ≤ |(reducedSymbol Q ξ).adjugate r c|)
    (hroot : κ ≤ fderiv ℝ (reducedDeterminant Q) ξ ν) :
    μ * κ ≤ |adaptedTimeCoefficient Q ξ r c ν| ∧
      adaptedTimeCoefficient Q ξ r c ν ≠ 0 ∧
      |(adaptedTimeCoefficient Q ξ r c ν)⁻¹| ≤ (μ * κ)⁻¹ := by
  have hne := abs_pos.mp (hμ.trans_le hminor)
  have hgap : μ * κ ≤ |adaptedTimeCoefficient Q ξ r c ν| := by
    rw [adaptedTimeCoefficient_eq_minor_mul_fderiv Q hQ ξ hchar hne, abs_mul]
    exact mul_le_mul hminor (hroot.trans (le_abs_self _)) hκ.le (abs_nonneg _)
  refine ⟨hgap, abs_pos.mp ((mul_pos hμ hκ).trans_le hgap), ?_⟩
  rw [abs_inv]
  simpa only [one_div] using one_div_le_one_div_of_le (mul_pos hμ hκ) hgap

/-- Dividing by the adapted coefficient cancels the chosen minor. Thus the
transport field is the determinant gradient normalized by the section normal,
as required by the actual Hamilton chart (`app:ch_waves:thm:leading`). -/
theorem transportField_div_adaptedTimeCoefficient
    (Q : Fin n → MetricTensor n) (hQ : ∀ i, (Q i).IsSymm) (ξ : Euclidean n)
    (hchar : reducedDeterminant Q ξ = 0) {r c : Fin n}
    (hminor : (reducedSymbol Q ξ).adjugate r c ≠ 0) (ν : Euclidean n) (a : Fin n) :
    transportField Q (leftNullvector (reducedSymbol Q ξ) r)
        (rightNullvector (reducedSymbol Q ξ) c) a /
        adaptedTimeCoefficient Q ξ r c ν =
      partialDeriv (reducedDeterminant Q) ξ a /
        fderiv ℝ (reducedDeterminant Q) ξ ν := by
  rw [transportField_eq_minor_mul_partialDeriv Q hQ ξ hchar hminor,
    adaptedTimeCoefficient_eq_minor_mul_fderiv Q hQ ξ hchar hminor]
  exact mul_div_mul_left _ _ hminor

end JanetCartan.NullTransport
