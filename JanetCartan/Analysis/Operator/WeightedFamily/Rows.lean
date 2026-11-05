module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Weighted squared row estimates

The finite-family step in `app:ch_mean_pairs:eq:mean-canonical-weighted-low`
and `app:ch_mean_pairs:eq:mean-canonical-weighted-C` of `paper.tex`.

The raw analytic estimate is an explicit input. Its squared coefficient `L`
is kept literally: for example, `C_s K^(2s+1)` or `C_s K^(2s+n)`.
The weighted row energy is an `ℓ²` norm, so boundedness of the row controls it
without a factor in the number of samples. No inverse weights are used.
-/

@[expose] public noncomputable section

namespace JanetCartan.WeightedFamily

variable {ι E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G]

/-- Summing squared raw estimates preserves their exact coefficient in
`app:ch_mean_pairs:eq:mean-canonical-weighted-low`. -/
theorem sum_weight_norm_sq_le (s : Finset ι) (μ : ι → ℝ)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (u : ι → E) (v : ι → F) {L : ℝ}
    (hraw : ∀ i ∈ s, ‖v i‖ ^ 2 ≤ L * ‖u i‖ ^ 2) :
    (∑ i ∈ s, μ i * ‖v i‖ ^ 2) ≤ L * ∑ i ∈ s, μ i * ‖u i‖ ^ 2 := by
  calc
    _ ≤ ∑ i ∈ s, μ i * (L * ‖u i‖ ^ 2) :=
      Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (hraw i hi) (hμ i hi)
    _ = _ := by simp_rw [mul_left_comm (μ _) L, Finset.mul_sum]

/-- The unsquared raw bound gives the coefficient `C²`, with no cardinality
loss (`app:ch_mean_pairs:eq:mean-canonical-weighted-low`). -/
theorem sum_weight_norm_sq_le_of_norm_le (s : Finset ι) (μ : ι → ℝ)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (u : ι → E) (v : ι → F) {C : ℝ}
    (hraw : ∀ i ∈ s, ‖v i‖ ≤ C * ‖u i‖) :
    (∑ i ∈ s, μ i * ‖v i‖ ^ 2) ≤ C ^ 2 * ∑ i ∈ s, μ i * ‖u i‖ ^ 2 := by
  apply sum_weight_norm_sq_le s μ hμ u v
  intro i hi
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hraw i hi))).mpr (hraw i hi)

/-- A squared-energy bound composes with the raw estimate without changing
its coefficient (`app:ch_mean_pairs:eq:mean-canonical-weighted-low`). -/
theorem sum_weight_norm_sq_le_of_energy_le (s : Finset ι) (μ : ι → ℝ)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (u : ι → E) (v : ι → F) {L B : ℝ} (hL : 0 ≤ L)
    (hraw : ∀ i ∈ s, ‖v i‖ ^ 2 ≤ L * ‖u i‖ ^ 2)
    (henergy : ∑ i ∈ s, μ i * ‖u i‖ ^ 2 ≤ B) :
    (∑ i ∈ s, μ i * ‖v i‖ ^ 2) ≤ L * B :=
  (sum_weight_norm_sq_le s μ hμ u v hraw).trans
    (mul_le_mul_of_nonneg_left henergy hL)

section FiniteFamily

variable [Fintype ι] [NormedSpace ℝ E]

/-- The square-root weighted `ℓ²` family appearing in the canonical row of
`app:ch_mean_pairs:defn:mean-canonical`. This definition allows zero weights. -/
def sqrtWeightedFamily (μ : ι → ℝ) (u : ι → E) : PiLp 2 (fun _ : ι ↦ E) :=
  WithLp.toLp 2 (fun i ↦ Real.sqrt (μ i) • u i)

/-- The exact weighted energy identity for
`app:ch_mean_pairs:eq:mean-canonical-weighted-low`. -/
theorem norm_sqrtWeightedFamily_sq (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (u : ι → E) :
    ‖sqrtWeightedFamily μ u‖ ^ 2 = ∑ i, μ i * ‖u i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  change ‖Real.sqrt (μ i) • u i‖ ^ 2 = μ i * ‖u i‖ ^ 2
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hμ i)]

/-- Raw squared estimates followed by a norm bound for the weighted family,
as in `app:ch_mean_pairs:eq:mean-canonical-weighted-low`. -/
theorem sum_weight_norm_sq_le_of_family_norm_le (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (u : ι → E) (v : ι → F) {L B : ℝ} (hL : 0 ≤ L)
    (hraw : ∀ i, ‖v i‖ ^ 2 ≤ L * ‖u i‖ ^ 2)
    (hfamily : ‖sqrtWeightedFamily μ u‖ ≤ B) :
    (∑ i, μ i * ‖v i‖ ^ 2) ≤ L * B ^ 2 := by
  apply sum_weight_norm_sq_le_of_energy_le Finset.univ μ (fun i _ ↦ hμ i) u v hL
    (fun i _ ↦ hraw i)
  rw [← norm_sqrtWeightedFamily_sq μ hμ u]
  exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hfamily)).mpr hfamily

/-- If the weighted data are the output of a bounded row, its operator norm
controls all squared raw estimates, without sample-count loss
(`app:ch_mean_pairs:eq:mean-canonical-weighted-low`). In the manuscript this
map is `A_K*`, and `q = Q₀ r`; constructing those maps is a separate input. -/
theorem sum_weight_norm_sq_le_of_row [NormedSpace ℝ G]
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (A : G →L[ℝ] PiLp 2 (fun _ : ι ↦ E)) (q : G) (u : ι → E) (v : ι → F)
    (hrow : sqrtWeightedFamily μ u = A q) {L : ℝ} (hL : 0 ≤ L)
    (hraw : ∀ i, ‖v i‖ ^ 2 ≤ L * ‖u i‖ ^ 2) :
    (∑ i, μ i * ‖v i‖ ^ 2) ≤ L * ‖A‖ ^ 2 * ‖q‖ ^ 2 := by
  have hfamily : ‖sqrtWeightedFamily μ u‖ ≤ ‖A‖ * ‖q‖ := by
    rw [hrow]
    exact A.le_opNorm q
  simpa only [mul_pow, mul_assoc] using
    sum_weight_norm_sq_le_of_family_norm_le μ hμ u v hL hraw hfamily

end FiniteFamily

end JanetCartan.WeightedFamily
