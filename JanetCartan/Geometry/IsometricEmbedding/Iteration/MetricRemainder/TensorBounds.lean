module

public import JanetCartan.Geometry.IsometricEmbedding.Basic

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Frobenius bounds for derivative tensors

The mixed and quadratic terms in `main:eq:metric-ledger` are built from the actual
coordinate derivatives. Their bounds use the operator norm of the differential;
the dimension factor converts the entry bound into the chosen Frobenius norm.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan

/-- `main:eq:metric-ledger`: the Frobenius norm of a real coordinate tensor. -/
theorem metricTensor_norm_eq_sqrt {n : ℕ} (A : MetricTensor n) :
    ‖A‖ = Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  simp only [Matrix.frobenius_norm_def, Real.rpow_two, Real.sqrt_eq_rpow]

/-- `main:eq:metric-ledger`: a uniform entry bound controls the Frobenius norm. -/
theorem metricTensor_norm_le_of_entries {n : ℕ} {A : MetricTensor n} {c : ℝ}
    (hc : 0 ≤ c) (hA : ∀ i j, ‖A i j‖ ≤ c) : ‖A‖ ≤ n * c := by
  rw [metricTensor_norm_eq_sqrt]
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  calc
    ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _i : Fin n, ∑ _j : Fin n, c ^ 2 := by
      exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        pow_le_pow_left₀ (norm_nonneg _) (hA i j) 2
    _ = (n * c) ^ 2 := by simp; ring

/-- `main:eq:metric-ledger`: Cauchy–Schwarz for the actual tensor contraction. -/
theorem abs_tensorPairing_le {n : ℕ} (A B : MetricTensor n) :
    |tensorPairing A B| ≤ ‖A‖ * ‖B‖ := by
  calc
    |tensorPairing A B| ≤ ∑ i, ∑ j, ‖A i j‖ * ‖B i j‖ := by
      simpa only [tensorPairing, Real.norm_eq_abs, abs_mul] using
        (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i ↦ ∑ j, A i j * B i j)).trans
          (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ‖A‖ * ‖B‖ := by
      simpa only [metricTensor_norm_eq_sqrt, Fintype.sum_prod_type] using
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun ij : Fin n × Fin n ↦ ‖A ij.1 ij.2‖)
          (fun ij : Fin n × Fin n ↦ ‖B ij.1 ij.2‖)

/-- `main:eq:joint-physical-profile`: coordinate derivatives are bounded by the differential. -/
theorem norm_partialDeriv_le_fderiv {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (i : Fin n) : ‖partialDeriv F x i‖ ≤ ‖fderiv ℝ F x‖ := by
  simpa [partialDeriv, PiLp.norm_single] using
    (fderiv ℝ F x).le_opNorm (EuclideanSpace.single i 1)

/-- `main:eq:metric-ledger`: the quadratic derivative tensor has a Frobenius bound. -/
theorem norm_inducedMetric_le {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) : ‖inducedMetric F x‖ ≤ n * ‖fderiv ℝ F x‖ ^ 2 := by
  apply metricTensor_norm_le_of_entries (sq_nonneg _)
  intro i j
  exact (norm_inner_le_norm _ _).trans (by
    simpa only [pow_two] using mul_le_mul
      (norm_partialDeriv_le_fderiv F x i) (norm_partialDeriv_le_fderiv F x j)
      (norm_nonneg _) (norm_nonneg _))

/-- `main:eq:metric-ledger`: the symmetrized mixed derivative tensor has a Frobenius bound. -/
theorem norm_linearizedMetric_le {n N : ℕ} (F Y : Euclidean n → Euclidean N)
    (x : Euclidean n) :
    ‖linearizedMetric F Y x‖ ≤ 2 * n * ‖fderiv ℝ F x‖ * ‖fderiv ℝ Y x‖ := by
  have h (G H : Euclidean n → Euclidean N) (i j : Fin n) :
      ‖inner ℝ (partialDeriv G x i) (partialDeriv H x j)‖ ≤
        ‖fderiv ℝ G x‖ * ‖fderiv ℝ H x‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul
      (norm_partialDeriv_le_fderiv G x i) (norm_partialDeriv_le_fderiv H x j)
      (norm_nonneg _) (norm_nonneg _))
  calc
    _ ≤ n * (2 * ‖fderiv ℝ F x‖ * ‖fderiv ℝ Y x‖) := by
      apply metricTensor_norm_le_of_entries (by positivity)
      intro i j
      exact (norm_add_le _ _).trans ((add_le_add (h F Y i j) (h Y F i j)).trans_eq
        (by ring))
    _ = _ := by ring

end JanetCartan
