module
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.JointJets
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.SourceDecay
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
open scoped ContDiff Matrix.Norms.Frobenius
/-!
# Source derivative bounds for literal test integrals

The consumer is frequency integrability in `SourceExpansion.LiteralLimit`.
These bounds include the actual test-function product derivatives in
`app:ch_regular_base:thm:actual-calculus`, Step 1.
-/
@[expose] public noncomputable section
open MeasureTheory
open JanetCartan.AmplitudeBound
namespace JanetCartan.FourierIntegral.SourceExpansion
variable {n : ℕ}
private theorem iteratedFDeriv_on_coordinate_vectors {f : Euclidean n → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ) (a : Fin k → Fin n) (x : Euclidean n) :
    iteratedFDeriv ℝ k f x (fun i ↦ EuclideanSpace.single (a i) 1) =
      euclideanCoordinateDerivList (List.ofFn a) f x := by
  induction k generalizing x with
  | zero => simp [euclideanCoordinateDerivList, iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [List.ofFn_succ, euclideanCoordinateDerivList, iteratedFDeriv_succ_apply_left]
    have he : euclideanCoordinateDerivList (List.ofFn (fun i ↦ a i.succ)) f =
        fun y ↦ iteratedFDeriv ℝ k f y (fun i ↦ EuclideanSpace.single (a i.succ) 1) :=
      funext fun y ↦ (ih _ y).symm
    rw [he]
    exact (fderiv_continuousMultilinear_apply_const_apply
      (ContDiff.differentiable_iteratedFDeriv (show (k : ℕ∞ω) < ∞ from WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top k)) hf).differentiableAt _ _).symm

private theorem norm_multilinear_le_coordinate_bound {k : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ Euclidean n) ℂ)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ a : Fin k → Fin n, ‖T (fun i ↦ EuclideanSpace.single (a i) 1)‖ ≤ B) :
    ‖T‖ ≤ (n : ℝ)^k * B := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have he (i : Fin k) : v i = ∑ j : Fin n, (v i j) • EuclideanSpace.single j 1 := by
    simpa using ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (v i)).symm
  calc
    _ = ‖T (fun i ↦ ∑ j : Fin n, (v i j) • EuclideanSpace.single j 1)‖ := by
      congr 2; funext i; exact he i
    _ ≤ ∑ a : Fin k → Fin n, ‖T (fun i ↦ (v i (a i)) • EuclideanSpace.single (a i) 1)‖ := by
      rw [T.map_sum]; exact norm_sum_le _ _
    _ ≤ ∑ _a : Fin k → Fin n, (∏ i, ‖v i‖) * B := by
      apply Finset.sum_le_sum
      intro a _
      rw [T.map_smul_univ, norm_smul, norm_prod]
      exact mul_le_mul (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ PiLp.norm_apply_le (v i) (a i)))
        (hb a) (norm_nonneg _) (by positivity)
    _ = _ := by simp; ring

/-- Coordinate symbol bounds control the Fréchet derivatives used by source
integration by parts (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem norm_iteratedFDeriv_le_source_coordinate_bound
    {f : Euclidean n → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ is : List (Fin n), is.length = k → ∀ y,
      ‖euclideanCoordinateDerivList is f y‖ ≤ B) (y : Euclidean n) :
    ‖iteratedFDeriv ℝ k f y‖ ≤ (n : ℝ)^k * B := by
  apply norm_multilinear_le_coordinate_bound _ hB
  intro a
  rw [iteratedFDeriv_on_coordinate_vectors hf]
  exact hb _ (List.length_ofFn) y

/-- The primitive full-symbol bound controls each scalar source derivative,
without changing the Frobenius convention or any source cutoff
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem norm_iteratedFDeriv_fullAmplitude_entry_le {r : ℕ}
    (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2)) {M : ℕ} {B : ℝ} (hb : HasFullSourceSymbolBound A M B)
    (k : ℕ) (hk : k ≤ M) (x η y : Euclidean n) (i j : Fin r) :
    ‖iteratedFDeriv ℝ k (fun z ↦ A x z η i j) y‖ ≤ (n : ℝ)^k * B := by
  have hB : 0 ≤ B := by
    have h := hb [] [] (by simp) x y η
    change 1 * ‖A x y η‖ ≤ B at h
    exact (norm_nonneg (A x y η)).trans (by simpa using h)
  apply norm_iteratedFDeriv_le_source_coordinate_bound
    (contDiff_fullAmplitudeParameterJet_entry A hA [] x η i j) k hB
  intro is his z
  have h := hb [] is (by simpa [his] using hk) x z η
  exact (norm_matrixEntry_le_frobenius _ i j).trans (by
    simpa [coefficientCovectorWeight, fullAmplitudeParameterJet,
      matrixCoefficientJet, scalarCoefficientJet] using h)

/-- The finite Leibniz budget includes derivatives of the actual test function.
It is uniform in the output and frequency parameters and is consumed by the
literal frequency majorant (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem sourceDerivativeMass_mul_le {f v : Euclidean n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (N : ℕ) {B : ℝ}
    (hb : ∀ k ≤ N, ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ (n : ℝ)^k * B) :
    Pseudodifferential.sourceDerivativeMass (fun y ↦ f y * v y) N ≤
      ∑ k ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (k + 1),
        ((k.choose l : ℝ) * ((n : ℝ)^l * B)) *
          ∫ y, ‖iteratedFDeriv ℝ (k-l) v y‖ := by
  classical
  have hi (k : ℕ) : Integrable (iteratedFDeriv ℝ k v) :=
    (hv.continuous_iteratedFDeriv (by simp)).integrable_of_hasCompactSupport
      (hvc.iteratedFDeriv k)
  unfold Pseudodifferential.sourceDerivativeMass
  apply Finset.sum_le_sum
  intro k hk
  have hki : Integrable (fun y ↦ ‖iteratedFDeriv ℝ k (fun y ↦ f y * v y) y‖) :=
    ((hf.mul hv).continuous_iteratedFDeriv (by simp)).integrable_of_hasCompactSupport
      ((hvc.mul_left).iteratedFDeriv k) |>.norm
  calc
    _ ≤ ∫ y, ∑ l ∈ Finset.range (k+1),
        ((k.choose l : ℝ) * ((n : ℝ)^l * B)) * ‖iteratedFDeriv ℝ (k-l) v y‖ := by
      apply integral_mono hki (integrable_finsetSum _ fun l _ ↦ (hi (k-l)).norm.const_mul _)
      intro y
      apply (norm_iteratedFDeriv_mul_le hf hv y (by simp : (k : ℕ∞ω) ≤ ∞)).trans
      apply Finset.sum_le_sum
      intro l hl
      gcongr
      exact hb l (by have := Finset.mem_range.mp hk; have := Finset.mem_range.mp hl; omega) y
    _ = _ := by
      rw [integral_finsetSum _ (fun l _ ↦ (hi (k-l)).norm.const_mul _)]
      simp_rw [integral_const_mul]

end JanetCartan.FourierIntegral.SourceExpansion
