module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Tactic.Ring

/-!
# Finite weighted canonical rows

The Hilbert-space algebra of `main:prop:canonical` and
`app:ch_mean_pairs:defn:mean-canonical`. The row acts from the finite Hilbert sum
of the raw spaces to the output space. Its component adjoints are taken before
applying the Fourier input maps, and no inverse sample weight is used.

This module does not construct the analytic wave maps or prove their raw bounds.
The estimates below transfer supplied raw bounds through the canonical adjoints.
-/

@[expose] public noncomputable section

open scoped BigOperators InnerProductSpace

namespace JanetCartan.CanonicalRow

variable {ι : Type*} [Fintype ι]
variable {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
  [∀ i, InnerProductSpace ℝ (Raw i)]
variable {Output : Type*} [NormedAddCommGroup Output]
  [InnerProductSpace ℝ Output]

/-- The row `A_K = (√μ_j A_{j,K})_j` of `app:ch_mean_pairs:defn:mean-canonical`,
with the raw Hilbert sum and output space explicit. -/
def weightedRow (μ : ι → ℝ) (A : ∀ i, Raw i →L[ℝ] Output) :
    PiLp 2 Raw →L[ℝ] Output :=
  ∑ i, Real.sqrt (μ i) • (A i).comp (PiLp.proj 2 Raw i)

/-- Evaluation of the finite row in `app:ch_mean_pairs:defn:mean-canonical`. -/
theorem weightedRow_apply (μ : ι → ℝ) (A : ∀ i, Raw i →L[ℝ] Output)
    (v : PiLp 2 Raw) :
    weightedRow μ A v = ∑ i, Real.sqrt (μ i) • A i (v i) := by
  simp [weightedRow]

variable [∀ i, CompleteSpace (Raw i)] [CompleteSpace Output]

/-- The adjoint column of the row in `app:ch_mean_pairs:defn:mean-canonical`. -/
theorem weightedRow_adjoint_apply (μ : ι → ℝ) (A : ∀ i, Raw i →L[ℝ] Output)
    (q : Output) :
    (weightedRow μ A).adjoint q =
      WithLp.toLp 2 (fun i ↦ Real.sqrt (μ i) • (A i).adjoint q) := by
  apply ext_inner_right ℝ
  intro v
  simp only [ContinuousLinearMap.adjoint_inner_left, weightedRow_apply,
    inner_sum, real_inner_smul_right, PiLp.inner_apply,
    real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]

/-- Each coordinate of the real Hilbert adjoint has the square-root row weight
(`app:ch_mean_pairs:defn:mean-canonical`). -/
@[simp] theorem weightedRow_adjoint_apply_component (μ : ι → ℝ)
    (A : ∀ i, Raw i →L[ℝ] Output) (q : Output) (i : ι) :
    (weightedRow μ A).adjoint q i = Real.sqrt (μ i) • (A i).adjoint q := by
  rw [weightedRow_adjoint_apply]

/-- Exact normal-operator formula in `main:eq:canonical-identity`.
Nonnegative weights suffice, including zero weights. -/
theorem weightedRow_normal_apply (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (A : ∀ i, Raw i →L[ℝ] Output) (q : Output) :
    weightedRow μ A ((weightedRow μ A).adjoint q) =
      ∑ i, μ i • A i ((A i).adjoint q) := by
  rw [weightedRow_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [weightedRow_adjoint_apply_component, map_smul, smul_smul,
    Real.mul_self_sqrt (hμ i)]

/-- Operator form of the exact normal formula of `main:prop:canonical`. -/
theorem weightedRow_comp_adjoint (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (A : ∀ i, Raw i →L[ℝ] Output) :
    (weightedRow μ A).comp (weightedRow μ A).adjoint =
      ∑ i, μ i • (A i).comp (A i).adjoint := by
  ext q
  simpa using weightedRow_normal_apply μ hμ A q

/-- The weighted sum of squared raw canonical components is exactly the squared
adjoint norm (`app:ch_mean_pairs:eq:mean-canonical-weighted-low`). -/
theorem sum_weighted_adjoint_norm_sq (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (A : ∀ i, Raw i →L[ℝ] Output) (q : Output) :
    ∑ i, μ i * ‖(A i).adjoint q‖ ^ 2 = ‖(weightedRow μ A).adjoint q‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  rw [weightedRow_adjoint_apply_component, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hμ i)]

/-- The row norm controls the squared component norms without an individual
inverse weight (`app:ch_mean_pairs:eq:mean-canonical-weighted-low`). -/
theorem sum_weighted_adjoint_norm_sq_le (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (A : ∀ i, Raw i →L[ℝ] Output) (q : Output) :
    ∑ i, μ i * ‖(A i).adjoint q‖ ^ 2 ≤ ‖weightedRow μ A‖ ^ 2 * ‖q‖ ^ 2 := by
  rw [sum_weighted_adjoint_norm_sq μ hμ A q, ← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _) _
  simpa using (weightedRow μ A).adjoint.le_opNorm q

section Estimates

/-- Squared raw estimates may be summed before applying the row norm, as in
`app:ch_mean_pairs:eq:mean-canonical-weighted-low` and
`app:ch_mean_pairs:eq:mean-canonical-weighted-C`. The size may be a Sobolev norm
or a derivative seminorm; only its stated squared raw bound is used. -/
theorem sum_weighted_size_sq_le_adjoint (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (A : ∀ i, Raw i →L[ℝ] Output) (size : ∀ i, Raw i → ℝ) {c : ℝ}
    (hraw : ∀ i v, size i v ^ 2 ≤ c * ‖v‖ ^ 2) (q : Output) :
    ∑ i, μ i * size i ((A i).adjoint q) ^ 2 ≤
      c * ‖(weightedRow μ A).adjoint q‖ ^ 2 := by
  rw [← sum_weighted_adjoint_norm_sq μ hμ A q, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    μ i * size i ((A i).adjoint q) ^ 2 ≤
        μ i * (c * ‖(A i).adjoint q‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hraw i _) (hμ i)
    _ = c * (μ i * ‖(A i).adjoint q‖ ^ 2) := by ring

/-- The row bound closes the squared raw estimate
(`app:ch_mean_pairs:eq:mean-canonical-weighted-low`,
`app:ch_mean_pairs:eq:mean-canonical-weighted-C`). -/
theorem sum_weighted_size_sq_le (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (A : ∀ i, Raw i →L[ℝ] Output) (size : ∀ i, Raw i → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hraw : ∀ i v, size i v ^ 2 ≤ c * ‖v‖ ^ 2) (q : Output) :
    ∑ i, μ i * size i ((A i).adjoint q) ^ 2 ≤
      c * (‖weightedRow μ A‖ ^ 2 * ‖q‖ ^ 2) := by
  refine (sum_weighted_size_sq_le_adjoint μ hμ A size hraw q).trans ?_
  apply mul_le_mul_of_nonneg_left _ hc
  rw [← sum_weighted_adjoint_norm_sq μ hμ A q]
  exact sum_weighted_adjoint_norm_sq_le μ hμ A q

/-- Specialization to raw maps into normed spaces, with the raw bound squared
before summation (`main:prop:canonical`). No completeness or Hilbert structure
is needed on the physical target spaces. -/
theorem sum_weighted_map_norm_sq_le
    {Physical : ι → Type*} [∀ i, SeminormedAddCommGroup (Physical i)]
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (A : ∀ i, Raw i →L[ℝ] Output)
    (G : ∀ i, Raw i → Physical i) {C : ℝ} (hC : 0 ≤ C)
    (hG : ∀ i v, ‖G i v‖ ≤ C * ‖v‖) (q : Output) :
    ∑ i, μ i * ‖G i ((A i).adjoint q)‖ ^ 2 ≤
      C ^ 2 * (‖weightedRow μ A‖ ^ 2 * ‖q‖ ^ 2) := by
  apply sum_weighted_size_sq_le μ hμ A (fun i v ↦ ‖G i v‖) (sq_nonneg C)
  intro i v
  simpa [mul_pow] using
    (sq_le_sq₀ (norm_nonneg (G i v)) (mul_nonneg hC (norm_nonneg v))).2 (hG i v)

end Estimates

section WaveMaps

variable {Data Physical : ι → Type*}
  [∀ i, NormedAddCommGroup (Data i)] [∀ i, NormedSpace ℝ (Data i)]
  [∀ i, NormedAddCommGroup (Physical i)] [∀ i, NormedSpace ℝ (Physical i)]

/-- Form `A_j v` from the Fourier input, current demodulated derivative, and
linear response maps, in that order (`app:ch_mean_pairs:defn:mean-canonical`).
The response map represents `D ↦ C[2 sym Re(B_j* D)]`. -/
def waveComponent (input : ∀ i, Raw i →L[ℝ] Data i)
    (wave : ∀ i, Data i →L[ℝ] Physical i)
    (response : ∀ i, Physical i →L[ℝ] Output) (i : ι) : Raw i →L[ℝ] Output :=
  (response i).comp ((wave i).comp (input i))

/-- The initial datum `f_j[q] = B_jⁱⁿ A_j* q` in
`app:ch_mean_pairs:eq:mean-current-canonical`. There is no sample weight in
this definition. -/
def canonicalData (A : ∀ i, Raw i →L[ℝ] Output)
    (input : ∀ i, Raw i →L[ℝ] Data i) (q : Output) (i : ι) : Data i :=
  input i ((A i).adjoint q)

/-- The current derivative change `D_j[q]` in
`app:ch_mean_pairs:eq:mean-current-canonical`, using the same wave map as `A_j`. -/
def canonicalDerivative (A : ∀ i, Raw i →L[ℝ] Output)
    (input : ∀ i, Raw i →L[ℝ] Data i)
    (wave : ∀ i, Data i →L[ℝ] Physical i) (q : Output) (i : ι) : Physical i :=
  wave i (canonicalData A input q i)

/-- The canonical data synthesize the exact weighted normal operator, with the
paper's weights and with no inverse weight (`main:eq:canonical-identity`). -/
theorem canonical_response_eq_normal (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (input : ∀ i, Raw i →L[ℝ] Data i)
    (wave : ∀ i, Data i →L[ℝ] Physical i)
    (response : ∀ i, Physical i →L[ℝ] Output) (q : Output) :
    let A := waveComponent input wave response
    ∑ i, μ i • response i (canonicalDerivative A input wave q i) =
      weightedRow μ A ((weightedRow μ A).adjoint q) := by
  dsimp only
  rw [weightedRow_normal_apply μ hμ]
  rfl

/-- Adding the fixed auxiliary response gives `E_K q`, the complete linear
response in `app:ch_mean_pairs:defn:mean-canonical`. -/
theorem auxiliary_add_canonical_response (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (input : ∀ i, Raw i →L[ℝ] Data i)
    (wave : ∀ i, Data i →L[ℝ] Physical i)
    (response : ∀ i, Physical i →L[ℝ] Output)
    (auxiliary : Output →L[ℝ] Output) (q : Output) :
    let A := waveComponent input wave response
    auxiliary q + ∑ i, μ i • response i (canonicalDerivative A input wave q i) =
      (auxiliary + (weightedRow μ A).comp (weightedRow μ A).adjoint) q := by
  dsimp only
  rw [canonical_response_eq_normal μ hμ]
  rfl

/-- The subtraction form `(E_K - F_{0,K}) q` of
`main:eq:canonical-identity`, for any fixed auxiliary operator. -/
theorem canonical_response_eq_normal_sub_auxiliary
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (input : ∀ i, Raw i →L[ℝ] Data i)
    (wave : ∀ i, Data i →L[ℝ] Physical i)
    (response : ∀ i, Physical i →L[ℝ] Output)
    (auxiliary : Output →L[ℝ] Output) (q : Output) :
    let A := waveComponent input wave response
    ∑ i, μ i • response i (canonicalDerivative A input wave q i) =
      ((auxiliary + (weightedRow μ A).comp (weightedRow μ A).adjoint) - auxiliary) q := by
  dsimp only
  rw [add_sub_cancel_left]
  exact canonical_response_eq_normal μ hμ input wave response q

/-- The canonical derivative estimate obtained from the uniform raw bound in
`app:ch_mean_pairs:eq:mean-current-raw`. The raw bound and the row norm remain
explicit inputs to the analytic application. -/
theorem sum_weighted_canonicalDerivative_norm_sq_le
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (A : ∀ i, Raw i →L[ℝ] Output)
    (input : ∀ i, Raw i →L[ℝ] Data i)
    (wave : ∀ i, Data i →L[ℝ] Physical i) {C : ℝ} (hC : 0 ≤ C)
    (hraw : ∀ i v, ‖wave i (input i v)‖ ≤ C * ‖v‖) (q : Output) :
    ∑ i, μ i * ‖canonicalDerivative A input wave q i‖ ^ 2 ≤
      C ^ 2 * (‖weightedRow μ A‖ ^ 2 * ‖q‖ ^ 2) :=
  sum_weighted_map_norm_sq_le μ hμ A (fun i v ↦ wave i (input i v)) hC hraw q

end WaveMaps

end JanetCartan.CanonicalRow
