module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Derivatives.SobolevComparison.Hilbert

/-!
# Jet and Sobolev comparisons for Frobenius matrices

For `main:lem:mean-recurrence` in paper.tex, matrix norms are the actual Frobenius
norms. Nested L² coordinates give a real Hilbert realization without changing
those norms. The resulting comparisons apply to real and complex rectangular
matrices, including empty row or column types.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix.Norms.Frobenius

namespace JanetCartan.CurrentMean

variable {m n E : Type*} [Fintype m] [Fintype n]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `main:lem:mean-recurrence`: nested L² coordinates realize Frobenius matrices
as a real Hilbert space. Used by `matrixFrobeniusInnerProductSpace`. -/
def matrixFrobeniusHilbertMap : Matrix m n E →ₗ[ℝ]
    PiLp 2 (fun _ : m ↦ PiLp 2 (fun _ : n ↦ E)) where
  toFun A := WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `main:lem:mean-recurrence`: the Hilbert realization preserves exactly the
existing Frobenius norm, with no norm-equivalence constants. -/
theorem norm_matrixFrobeniusHilbertMap (A : Matrix m n E) :
    ‖matrixFrobeniusHilbertMap A‖ = ‖A‖ := rfl

/-- `main:lem:mean-recurrence`: a real inner product compatible with the existing
Frobenius norm. This is installed only locally in the comparison proofs, so it
does not select a global matrix norm. -/
@[instance_reducible]
def matrixFrobeniusInnerProductSpace : InnerProductSpace ℝ (Matrix m n E) where
  inner A B := inner ℝ (matrixFrobeniusHilbertMap A) (matrixFrobeniusHilbertMap B)
  norm_sq_eq_re_inner A := norm_sq_eq_re_inner (matrixFrobeniusHilbertMap A)
  conj_inner_symm A B := inner_conj_symm _ _
  add_left A B C := by rw [map_add, inner_add_left]
  smul_left A B r := by rw [map_smul, inner_smul_left]

variable {d : ℕ} [FiniteDimensional ℝ E]

/-- `main:lem:mean-recurrence`: the uniform jet-to-Sobolev comparison for
Frobenius matrices. In particular `E = ℂ` gives the higher factor in the
weighted Hermitian product estimate, without a Fourier-support premise. -/
theorem periodicL2Norm_periodicJet_matrix_le_sobolev_uniform (S : ℕ)
    {f : Torus d → Matrix m n E} (hf : IsSmoothPeriodic f)
    {r t : ℕ} (hrt : r ≤ t) (htS : t ≤ S) :
    periodicL2Norm (periodicJet r f) ≤
      periodicJetSobolevConstant d S * periodicSobolevNorm t f := by
  let := matrixFrobeniusInnerProductSpace (m := m) (n := n) (E := E)
  exact periodicL2Norm_periodicJet_le_sobolev_uniform S hf hrt htS

/-- `main:lem:mean-recurrence`: the reverse comparison for Frobenius matrices.
In particular `E = ℝ` applies to the real tensor resulting from the Hermitian
product. Smoothness supplies all Fourier summability. -/
theorem periodicSobolevNorm_matrix_le_sum_periodicJet_uniform (S : ℕ)
    {f : Torus d → Matrix m n E} (hf : IsSmoothPeriodic f) :
    periodicSobolevNorm S f ≤ sobolevPeriodicJetConstant d S *
      ∑ j ∈ Finset.range (S + 1), periodicL2Norm (periodicJet j f) := by
  let := matrixFrobeniusInnerProductSpace (m := m) (n := n) (E := E)
  exact periodicSobolevNorm_le_sum_periodicJet_uniform S hf

end JanetCartan.CurrentMean
