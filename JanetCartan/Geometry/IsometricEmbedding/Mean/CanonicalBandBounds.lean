module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalBandBounds.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weighted Sobolev and derivative bounds for one fixed canonical row

Conditional proofs of the weighted conclusions in `main:prop:canonical`,
`app:ch_mean_pairs:eq:mean-canonical-weighted-low`, and
`app:ch_mean_pairs:eq:mean-canonical-weighted-C`. The maps `A`, `G`, and `Q0`
are fixed throughout each statement. The complete normal decomposition, positivity,
uniform normal comparison, L² inverse bound, and raw physical bounds are inputs.
Their actual producers and the consumers responsible for instantiation are listed
in `CanonicalBandBounds/Basic.lean`; these deductions do not construct the maps.

The physical sizes are parameters so that the consumers can insert their actual
Sobolev norms and derivative seminorms, with the fixed observation cutoff included.
Only nonnegativity and the displayed raw bounds are used. The finite sums are
literal: no new smooth-family space or weighted-norm convention is introduced,
and there is no identification of torus data with Euclidean initial data.

If `M`, `ε`, `L`, and the raw constants are uniform, the displayed constants are
uniform in the sample count, the smallest sample weight, and mean accuracy. Neither
individual component bounds nor higher regularity of the continuum inverse occur.
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

/-- Common band calculation for `main:prop:canonical`. Squaring the raw estimate
`size (G v) ≤ c Kᵃ ‖v‖` gives exponent `2a` in the literal weighted sum. Its
square root has constant `c √(M + ε) L`, independent of the weights and band. -/
theorem weighted_band_bounds
    {Physical : ι → Type*} (G : ∀ i, Raw i → Physical i)
    (size : ∀ i, Physical i → ℝ) (hsize : ∀ i u, 0 ≤ size i u)
    {K c a : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hraw : ∀ i v, size i (G i v) ≤ c * K ^ a * ‖v‖) (r : Output) :
    (∑ i, μ i * size i (G i ((A i).adjoint (Q0 r))) ^ 2 ≤
      (c ^ 2 * (M + ε) * L ^ 2) * K ^ (2 * a) * ‖r‖ ^ 2) ∧
    (Real.sqrt (∑ i, μ i * size i (G i ((A i).adjoint (Q0 r))) ^ 2) ≤
      (c * Real.sqrt (M + ε) * L) * K ^ a * ‖r‖) := by
  have hca : 0 ≤ c * K ^ a := mul_nonneg hc (Real.rpow_nonneg hK _)
  have hpower : (K ^ a) ^ 2 = K ^ (2 * a) := by
    rw [← Real.rpow_mul_natCast hK a 2]
    congr 1
    push_cast
    ring
  constructor
  · calc
      _ ≤ (c * K ^ a) ^ 2 * (M + ε) * L ^ 2 * ‖r‖ ^ 2 :=
        sum_weighted_physical_size_sq_le μ hμ A complete auxiliary reference Q0
          hdecomposition hauxiliary hreference hcomparison hQ0 G size hsize hca hraw r
      _ = _ := by rw [mul_pow, hpower]; ring
  · calc
      _ ≤ (c * K ^ a) * Real.sqrt (M + ε) * L * ‖r‖ :=
        sqrt_sum_weighted_physical_size_sq_le μ hμ A complete auxiliary reference Q0
          hdecomposition hauxiliary hreference hcomparison hQ0 G size hsize hca hraw r
      _ = _ := by ring

/-- The squared-sum estimate `app:ch_mean_pairs:eq:mean-canonical-weighted-low`
and the weighted Hˢ conclusion of `main:prop:canonical`, with explicit constants.
`sobolevSize i` is to be instantiated with the physical Hˢ norm (including the
observation cutoff); the only analytic input about it is the stated raw bound. -/
theorem weighted_sobolev_band_bounds
    {Physical : ι → Type*} (G : ∀ i, Raw i → Physical i)
    (s : ℕ) (sobolevSize : ∀ i, Physical i → ℝ)
    (hsize : ∀ i u, 0 ≤ sobolevSize i u)
    {K c : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hraw : ∀ i v, sobolevSize i (G i v) ≤ c * K ^ ((s : ℝ) + 1 / 2) * ‖v‖)
    (r : Output) :
    (∑ i, μ i * sobolevSize i (G i ((A i).adjoint (Q0 r))) ^ 2 ≤
      (c ^ 2 * (M + ε) * L ^ 2) * K ^ (2 * (s : ℝ) + 1) * ‖r‖ ^ 2) ∧
    (Real.sqrt (∑ i, μ i * sobolevSize i (G i ((A i).adjoint (Q0 r))) ^ 2) ≤
      (c * Real.sqrt (M + ε) * L) * K ^ ((s : ℝ) + 1 / 2) * ‖r‖) := by
  have hexponent : 2 * ((s : ℝ) + 1 / 2) = 2 * (s : ℝ) + 1 := by ring
  simpa only [hexponent] using
    weighted_band_bounds μ hμ A complete auxiliary reference Q0 hdecomposition
      hauxiliary hreference hcomparison hQ0 G sobolevSize hsize hK hc hraw r

/-- The squared-sum estimate `app:ch_mean_pairs:eq:mean-canonical-weighted-C`
and the weighted Cˢ conclusion of `main:prop:canonical`, with dimension `n`.
`derivativeSize i` is to be instantiated with the physical Cˢ seminorm after the
observation cutoff. The raw input norm is still the original Hilbert norm. -/
theorem weighted_derivative_band_bounds
    {Physical : ι → Type*} (G : ∀ i, Raw i → Physical i)
    (s n : ℕ) (derivativeSize : ∀ i, Physical i → ℝ)
    (hsize : ∀ i u, 0 ≤ derivativeSize i u)
    {K c : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hraw : ∀ i v, derivativeSize i (G i v) ≤
      c * K ^ ((s : ℝ) + (n : ℝ) / 2) * ‖v‖) (r : Output) :
    (∑ i, μ i * derivativeSize i (G i ((A i).adjoint (Q0 r))) ^ 2 ≤
      (c ^ 2 * (M + ε) * L ^ 2) * K ^ (2 * (s : ℝ) + n) * ‖r‖ ^ 2) ∧
    (Real.sqrt (∑ i, μ i * derivativeSize i (G i ((A i).adjoint (Q0 r))) ^ 2) ≤
      (c * Real.sqrt (M + ε) * L) * K ^ ((s : ℝ) + (n : ℝ) / 2) * ‖r‖) := by
  have hexponent : 2 * ((s : ℝ) + (n : ℝ) / 2) = 2 * (s : ℝ) + n := by ring
  simpa only [hexponent] using
    weighted_band_bounds μ hμ A complete auxiliary reference Q0 hdecomposition
      hauxiliary hreference hcomparison hQ0 G derivativeSize hsize hK hc hraw r

/-- Apply the band estimates to the existing `CanonicalRow.canonicalDerivative`
of `app:ch_mean_pairs:eq:mean-current-canonical`, retaining the actual initial
input map and physical wave map. Take `a = s + 1/2` for the Sobolev estimate or
`a = s + n/2` for the derivative estimate. No new canonical field is defined. -/
theorem canonicalDerivative_band_bounds
    {Data Physical : ι → Type*}
    [∀ i, NormedAddCommGroup (Data i)] [∀ i, NormedSpace ℝ (Data i)]
    [∀ i, NormedAddCommGroup (Physical i)] [∀ i, NormedSpace ℝ (Physical i)]
    (input : ∀ i, Raw i →L[ℝ] Data i) (wave : ∀ i, Data i →L[ℝ] Physical i)
    (size : ∀ i, Physical i → ℝ) (hsize : ∀ i u, 0 ≤ size i u)
    {K c a : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hraw : ∀ i v, size i (wave i (input i v)) ≤ c * K ^ a * ‖v‖) (r : Output) :
    (∑ i, μ i * size i (CanonicalRow.canonicalDerivative A input wave (Q0 r) i) ^ 2 ≤
      (c ^ 2 * (M + ε) * L ^ 2) * K ^ (2 * a) * ‖r‖ ^ 2) ∧
    (Real.sqrt (∑ i, μ i *
      size i (CanonicalRow.canonicalDerivative A input wave (Q0 r) i) ^ 2) ≤
      (c * Real.sqrt (M + ε) * L) * K ^ a * ‖r‖) :=
  weighted_band_bounds μ hμ A complete auxiliary reference Q0 hdecomposition
    hauxiliary hreference hcomparison hQ0 (fun i v ↦ wave i (input i v))
    size hsize hK hc hraw r

end JanetCartan.CanonicalBandBounds
