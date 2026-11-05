module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.MetricRemainder.TensorBounds
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.JetComposition
public import JanetCartan.Analysis.ContDiff.Norm.Products

/-!
# The induced metric preserves the derivative scale

The Leibniz step in `main:lem:smoothing`, used by
`exists_historyDefect_derivative_profile`: a baseline-one map profile gives a
baseline-zero metric profile. The two differentiated factors retain their separate
orders, and the tensor norm is the Frobenius norm.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
open Set

set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.DefectSmoothing

private def metricJetBilinear (n N : ℕ) :
    (Euclidean n →L[ℝ] Euclidean N) →L[ℝ]
      (Euclidean n →L[ℝ] Euclidean N) →L[ℝ] MetricTensor n := by
  let L : (Euclidean n →L[ℝ] Euclidean N) →ₗ[ℝ]
      (Euclidean n →L[ℝ] Euclidean N) →ₗ[ℝ] MetricTensor n := LinearMap.mk₂ ℝ
    (fun (A B : Euclidean n →L[ℝ] Euclidean N) ↦
      (fun i j ↦ inner ℝ (A (EuclideanSpace.single i 1))
        (B (EuclideanSpace.single j 1)) : MetricTensor n))
    (by intros; ext i j; simp [inner_add_left])
    (by intros; ext i j; simp [real_inner_smul_left])
    (by intros; ext i j; simp [inner_add_right])
    (by intros; ext i j; simp [inner_smul_right])
  exact L.mkContinuous₂ n (by
      intro A B
      apply (metricTensor_norm_le_of_entries (mul_nonneg (norm_nonneg A) (norm_nonneg B)) ?_).trans_eq
      · ring
      · intro i j
        change ‖inner ℝ (A (EuclideanSpace.single i 1))
          (B (EuclideanSpace.single j 1))‖ ≤ _
        exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (mul_le_mul
          (by simpa [PiLp.norm_single] using A.le_opNorm (EuclideanSpace.single i 1))
          (by simpa [PiLp.norm_single] using B.le_opNorm (EuclideanSpace.single j 1))
          (norm_nonneg _) (norm_nonneg _)))

/-- `main:lem:smoothing`, the Leibniz step for `main:eq:smoothing-high`:
constants for the actual induced metric follow from constants for the map with
baseline one. They precede the compact set, scale, and map. -/
theorem exists_inducedMetric_derivative_profile {n N : ℕ} (C : ℕ → ℝ)
    (hC : ∀ r, 0 ≤ C r) :
    ∃ B : ℕ → ℝ, (∀ r, 0 ≤ B r) ∧
      ∀ (K : Set (Euclidean n)), IsCompact K → ∀ (T : ℝ), 1 ≤ T →
      ∀ (F : Euclidean n → Euclidean N), ContDiff ℝ ∞ F →
        HasDerivativeProfile K F 1 T C →
        ∀ r, cNorm K r (inducedMetric F) ≤ B r * T ^ r := by
  let : NormedAddCommGroup (Euclidean n →L[ℝ] Euclidean N) := inferInstance
  let : NormedSpace ℝ (Euclidean n →L[ℝ] Euclidean N) := inferInstance
  let : NormedAddCommGroup ((Euclidean n →L[ℝ] Euclidean N) →L[ℝ] MetricTensor n) :=
    inferInstance
  let : NormedSpace ℝ ((Euclidean n →L[ℝ] Euclidean N) →L[ℝ] MetricTensor n) :=
    inferInstance
  let B : (Euclidean n →L[ℝ] Euclidean N) →L[ℝ]
      (Euclidean n →L[ℝ] Euclidean N) →L[ℝ] MetricTensor n := metricJetBilinear n N
  let A := fun r ↦ ‖B‖ * ∑ j ∈ Finset.range (r + 1),
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * C (i + 1) * C (j - i + 1)
  have hA : ∀ r, 0 ≤ A r := fun r ↦ mul_nonneg (norm_nonneg _) (Finset.sum_nonneg
    fun j _ ↦ Finset.sum_nonneg fun i _ ↦ mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hC _)) (hC _))
  refine ⟨A, hA, ?_⟩
  intro K hK T hT F hF hp r
  have hd : ContDiff ℝ r (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hs (i : ℕ) :
      sSup ((fun x ↦ ‖iteratedFDeriv ℝ i (fderiv ℝ F) x‖) '' K) ≤ C (i + 1) * T ^ i := by
    calc
      _ ≤ cNorm K i (fderiv ℝ F) := Finset.single_le_sum
        (fun k _ ↦ sSup_norm_iteratedFDeriv_nonneg K k (fderiv ℝ F))
        (Finset.mem_range.mpr (Nat.lt_succ_self i))
      _ ≤ cNorm K (i + 1) F := GeometricProfile.cNorm_fderiv_le K i F
      _ ≤ _ := by simpa using hp (i + 1)
  have heq : inducedMetric F = fun x ↦ B (fderiv ℝ F x) (fderiv ℝ F x) := rfl
  rw [heq]
  apply (cNorm_bilinear_le_sum B hK hd hd).trans
  calc
    _ ≤ ‖B‖ * ∑ j ∈ Finset.range (r + 1), ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (C (i + 1) * T ^ i) * (C (j - i + 1) * T ^ (j - i)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hs i) (Nat.cast_nonneg _))
        (hs (j - i)) (sSup_norm_iteratedFDeriv_nonneg K _ _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC _) (pow_nonneg (by linarith) _)))
    _ ≤ ‖B‖ * ∑ j ∈ Finset.range (r + 1), ∑ i ∈ Finset.range (j + 1),
        ((j.choose i : ℝ) * C (i + 1) * C (j - i + 1)) * T ^ r := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      calc
        _ = ((j.choose i : ℝ) * C (i + 1) * C (j - i + 1)) * T ^ j := by
          calc
            _ = ((j.choose i : ℝ) * C (i + 1) * C (j - i + 1)) *
                (T ^ i * T ^ (j - i)) := by ring
            _ = _ := by rw [← pow_add, Nat.add_sub_of_le hij]
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT hjr)
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC _)) (hC _))
    _ = A r * T ^ r := by simp only [A, Finset.sum_mul, mul_assoc]

end JanetCartan.DefectSmoothing
