module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange

/-!
# Weighted canonical bounds with an explicit L² inverse constant

The Hilbert-space deduction in `main:prop:canonical` and
`app:ch_mean_pairs:eq:mean-canonical-weighted-low`/`mean-canonical-weighted-C`.
The complete normal is supplied with its exact auxiliary-plus-row decomposition.
Only the L² operator norm of the fixed continuum inverse is used.

These are conditional deductions for `jc-current-canonical` and `jc-current-mean`.
The actual maps, decomposition, nonnegative auxiliary normal, uniform reference
and comparison bounds, and inverse bound must be supplied by
`jc-corrected-atoms`, `jc-raw-primary-fields`, `jc-simultaneous-sampling`, and
`jc-continuum-l2-inverse`. No raw input measure is changed here.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace

namespace JanetCartan.CanonicalBandBounds

variable {ι : Type*} [Fintype ι]
  {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
  [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]
  {Output : Type*} [NormedAddCommGroup Output]
  [InnerProductSpace ℝ Output] [CompleteSpace Output]

variable (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
  (A : ∀ i, Raw i →L[ℝ] Output)
  (complete auxiliary reference Q0 : Output →L[ℝ] Output)
  {M ε L : ℝ}
  (hdecomposition : complete = auxiliary + (CanonicalRow.weightedRow μ A).comp
    (CanonicalRow.weightedRow μ A).adjoint)
  (hauxiliary : ∀ q, 0 ≤ inner ℝ (auxiliary q) q)
  (hreference : ‖reference‖ ≤ M) (hcomparison : ‖complete - reference‖ ≤ ε)
  (hQ0 : ‖Q0‖ ≤ L)

include hμ hdecomposition hauxiliary hreference hcomparison hQ0

/-- The raw canonical energy in `app:ch_mean_pairs:eq:mean-canonical-weighted-low`
is bounded independently of the number of samples and of their smallest weight.
This uses the complete normal to bound the row, never an individual component. -/
theorem sum_weighted_adjoint_inverse_norm_sq_le (r : Output) :
    ∑ i, μ i * ‖(A i).adjoint (Q0 r)‖ ^ 2 ≤ (M + ε) * L ^ 2 * ‖r‖ ^ 2 := by
  have hnormal := hcomparison
  rw [hdecomposition] at hnormal
  have hnonneg : 0 ≤ M + ε := add_nonneg ((norm_nonneg _).trans hreference)
    ((norm_nonneg _).trans hcomparison)
  have hL : 0 ≤ L := (norm_nonneg _).trans hQ0
  have hrow := CanonicalChange.row_norm_le_of_normal_comparison
    (CanonicalRow.weightedRow μ A) auxiliary reference hauxiliary hreference hnormal
  have hq : ‖Q0 r‖ ≤ L * ‖r‖ := (Q0.le_opNorm r).trans
    (mul_le_mul_of_nonneg_right hQ0 (norm_nonneg _))
  have hadjoint : ‖(CanonicalRow.weightedRow μ A).adjoint (Q0 r)‖ ≤
      Real.sqrt (M + ε) * (L * ‖r‖) := by
    calc
      _ ≤ ‖(CanonicalRow.weightedRow μ A).adjoint‖ * ‖Q0 r‖ :=
        (CanonicalRow.weightedRow μ A).adjoint.le_opNorm _
      _ ≤ Real.sqrt (M + ε) * ‖Q0 r‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [ContinuousLinearMap.adjoint.norm_map] using hrow
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (Real.sqrt_nonneg _)
  rw [CanonicalRow.sum_weighted_adjoint_norm_sq μ hμ A]
  calc
    _ ≤ (Real.sqrt (M + ε) * (L * ‖r‖)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hadjoint
    _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hnonneg]; ring

/-- Square the supplied raw physical estimate before summation, then use the
complete normal comparison and the L² inverse bound. This is the common step of
`app:ch_mean_pairs:eq:mean-canonical-weighted-low` and
`app:ch_mean_pairs:eq:mean-canonical-weighted-C`. `size` can be the actual Sobolev
norm or the derivative seminorm after the fixed observation cutoff. -/
theorem sum_weighted_physical_size_sq_le
    {Physical : ι → Type*} (G : ∀ i, Raw i → Physical i)
    (size : ∀ i, Physical i → ℝ) (hsize : ∀ i u, 0 ≤ size i u)
    {C : ℝ} (hC : 0 ≤ C)
    (hraw : ∀ i v, size i (G i v) ≤ C * ‖v‖) (r : Output) :
    ∑ i, μ i * size i (G i ((A i).adjoint (Q0 r))) ^ 2 ≤
      C ^ 2 * (M + ε) * L ^ 2 * ‖r‖ ^ 2 := by
  have hnormal := hcomparison
  rw [hdecomposition] at hnormal
  have hnonneg : 0 ≤ M + ε := add_nonneg ((norm_nonneg _).trans hreference)
    ((norm_nonneg _).trans hcomparison)
  have hL : 0 ≤ L := (norm_nonneg _).trans hQ0
  have hraw_sq (i : ι) (v : Raw i) :
      size i (G i v) ^ 2 ≤ C ^ 2 * ‖v‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (hsize i _) (mul_nonneg hC (norm_nonneg _))).2 (hraw i v)
  calc
    _ ≤ C ^ 2 * (M + ε) * ‖Q0‖ ^ 2 * ‖r‖ ^ 2 :=
      CanonicalChange.sum_weighted_size_sq_le_of_normal_comparison μ hμ A
        auxiliary reference Q0 (fun i v ↦ size i (G i v)) (sq_nonneg C)
        hauxiliary hreference hnormal hraw_sq r
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hL).2 hQ0)
        (mul_nonneg (sq_nonneg _) hnonneg)) (sq_nonneg _)

/-- Square-root form of the weighted physical estimate in `main:prop:canonical`.
The explicit constant `C * √(M + ε) * L` has no sample-count, inverse-weight, or
mean-accuracy factor. Zero weights and empty families are allowed. -/
theorem sqrt_sum_weighted_physical_size_sq_le
    {Physical : ι → Type*} (G : ∀ i, Raw i → Physical i)
    (size : ∀ i, Physical i → ℝ) (hsize : ∀ i u, 0 ≤ size i u)
    {C : ℝ} (hC : 0 ≤ C)
    (hraw : ∀ i v, size i (G i v) ≤ C * ‖v‖) (r : Output) :
    Real.sqrt (∑ i, μ i * size i (G i ((A i).adjoint (Q0 r))) ^ 2) ≤
      C * Real.sqrt (M + ε) * L * ‖r‖ := by
  have hnonneg : 0 ≤ M + ε := add_nonneg ((norm_nonneg _).trans hreference)
    ((norm_nonneg _).trans hcomparison)
  have hL : 0 ≤ L := (norm_nonneg _).trans hQ0
  apply (Real.sqrt_le_left (by positivity)).2
  calc
    _ ≤ C ^ 2 * (M + ε) * L ^ 2 * ‖r‖ ^ 2 :=
      sum_weighted_physical_size_sq_le μ hμ A complete auxiliary reference Q0
        hdecomposition hauxiliary hreference hcomparison hQ0 G size hsize hC hraw r
    _ = _ := by simp only [mul_pow, Real.sq_sqrt hnonneg]

end JanetCartan.CanonicalBandBounds
