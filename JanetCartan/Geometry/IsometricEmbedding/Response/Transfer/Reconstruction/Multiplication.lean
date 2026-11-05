module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.Multiplication.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.Multiplication.Sums
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Coordinates

/-!
# Localized graded Sobolev multiplication

The scalar Euclidean multiplier estimate behind
`app:ch_response:eq:response-graded-displacement`,
`app:ch_response:eq:response-graded-derivative`, and
`app:ch_response:eq:response-graded-strain`. Only the coefficient is compactly
supported; the envelope is an actual Fourier Sobolev L² class. The coefficient
derivative budget is finite and the constant depends only on dimension and order.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential

namespace JanetCartan.IsometricEmbedding.Reconstruction

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- The dimension/order constant for the scalar multiplication used in
`app:ch_response:eq:response-reconstruction-grading`. -/
def localizedMultiplierConstant (d n : ℕ) : ℝ :=
  (1 + (d : ℝ) * (1 + 2 * Real.pi)) ^ n

/-- Positivity of the universal multiplier constant in
`app:ch_response:eq:response-reconstruction-grading`, including dimension zero. -/
theorem localizedMultiplierConstant_pos (d n : ℕ) :
    0 < localizedMultiplierConstant d n := by
  unfold localizedMultiplierConstant
  positivity

/-- The concrete finite-order multiplier estimate for
`app:ch_response:eq:response-graded-displacement`,
`app:ch_response:eq:response-graded-derivative`, and
`app:ch_response:eq:response-graded-strain`.
The mixed sum is `∑ k ≤ n, C (n-k) * ‖u‖_{H^k}`; coefficient bounds are
required only through order `n`. Product membership is a conclusion. -/
theorem localizedScalarProduct_integer_bound (n : ℕ)
    (c : E → ℂ) (hc : ContDiff ℝ ∞ c) (hcs : HasCompactSupport c)
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hbudget : ∀ is : List (Fin d), is.length ≤ n →
      ∀ x, ‖euclideanCoordinateDerivList is c x‖ ≤ C is.length)
    (u : L2) (hu : MemFourierSobolev (n : ℝ) u) :
    MemFourierSobolev (n : ℝ) (localizedScalarProduct c hc hcs u) ∧
      fourierSobolevNorm (n : ℝ) (localizedScalarProduct c hc hcs u) ≤
        localizedMultiplierConstant d n * mixedAmplitudeSobolevSum n C u := by
  induction n generalizing c C u with
  | zero =>
    constructor
    · simp
    · simpa [localizedMultiplierConstant, mixedAmplitudeSobolevSum] using
        norm_localizedScalarProduct_le c hc hcs u (hC 0) (hbudget [] (by simp))
  | succ n ih =>
    have hu' : MemFourierSobolev ((n : ℝ) + 1) u := by
      simpa only [Nat.cast_add, Nat.cast_one] using hu
    obtain ⟨du, hdu⟩ := hu'.exists_coordinateDerivatives (by positivity)
    let dc := fun i ↦ euclideanCoordinateDerivList [i] c
    let hdc := fun i ↦ contDiff_euclideanCoordinateDerivList hc [i]
    let hdcs := fun i ↦ hasCompactSupport_euclideanCoordinateDerivList hcs [i]
    have hdb (i : Fin d) (is : List (Fin d)) (hi : is.length ≤ n) (x : E) :
        ‖euclideanCoordinateDerivList is (dc i) x‖ ≤ C (is.length + 1) := by
      have h := hbudget (is ++ [i]) (by simp; omega) x
      simpa only [List.length_append, List.length_singleton,
        euclideanCoordinateDerivList_append] using h
    let v := localizedScalarProduct c hc hcs u
    let t := fun i ↦ localizedScalarProduct (dc i) (hdc i) (hdcs i) u
    let w := fun i ↦ t i + localizedScalarProduct c hc hcs (du i)
    have hun : MemFourierSobolev (n : ℝ) u := hu'.mono (by linarith)
    have hv := ih c hc hcs C hC (fun is hi ↦ hbudget is (by omega)) u hun
    have ht := fun i ↦ ih (dc i) (hdc i) (hdcs i) (fun j ↦ C (j + 1))
      (fun j ↦ hC _) (hdb i) u hun
    have hud := fun i ↦ ih c hc hcs C hC (fun is hi ↦ hbudget is (by omega))
      (du i) (hdu i).2
    have hwmem (i : Fin d) : MemFourierSobolev (n : ℝ) (w i) :=
      (ht i).1.add (hud i).1
    have hw (i : Fin d) : HasEuclideanL2CoordinateDerivative i v (w i) :=
      localizedScalarProduct_coordinateDerivative c hc hcs (hdu i).1
    have hnorm := fourierSobolevNorm_le_coordinateDerivatives (by positivity) hv.1 hwmem hw
    have hconst := (localizedMultiplierConstant_pos d n).le
    let S := mixedAmplitudeSobolevSum (n + 1) C u
    have hvnorm : fourierSobolevNorm (n : ℝ) v ≤ localizedMultiplierConstant d n * S :=
      hv.2.trans (mul_le_mul_of_nonneg_left (multiplier_sum_succ_le n hC hu) hconst)
    have hwnorm (i : Fin d) : fourierSobolevNorm (n : ℝ) (w i) ≤
        localizedMultiplierConstant d n * ((1 + 2 * Real.pi) * S) := by
      calc
        _ ≤ fourierSobolevNorm (n : ℝ) (t i) +
            fourierSobolevNorm (n : ℝ) (localizedScalarProduct c hc hcs (du i)) :=
          fourierSobolevNorm_add_le (ht i).1 (hud i).1
        _ ≤ localizedMultiplierConstant d n * S +
            localizedMultiplierConstant d n * ((2 * Real.pi) * S) := by
          apply add_le_add
          · exact (ht i).2.trans (mul_le_mul_of_nonneg_left
              (multiplier_sum_shift_le n hC u) hconst)
          · exact (hud i).2.trans (mul_le_mul_of_nonneg_left
              (multiplier_sum_derivative_le n hC (hdu i).1 hu) hconst)
        _ = _ := by ring
    constructor
    · simpa only [Nat.cast_add, Nat.cast_one] using
        hv.1.of_coordinateDerivatives (by positivity) hwmem hw
    · simp only [Nat.cast_add, Nat.cast_one]
      calc
        _ ≤ _ := hnorm
        _ ≤ localizedMultiplierConstant d n * S +
            ∑ _i : Fin d, localizedMultiplierConstant d n * ((1 + 2 * Real.pi) * S) :=
          add_le_add hvnorm (Finset.sum_le_sum fun i _ ↦ hwnorm i)
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            localizedMultiplierConstant, pow_succ]
          ring

/-- The scalar graded multiplier estimate used to assemble
`app:ch_response:eq:response-graded-displacement`,
`app:ch_response:eq:response-graded-derivative`, and
`app:ch_response:eq:response-graded-strain`.
The resulting constant is independent of `c`, `u`, `L`, `K`, and `A`.
Only derivative and envelope budgets through `n` are consumed. -/
theorem localizedScalarProduct_graded_bound (n : ℕ)
    (c : E → ℂ) (hc : ContDiff ℝ ∞ c) (hcs : HasCompactSupport c)
    (C B : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (hB : ∀ j, 0 ≤ B j)
    {A L K : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L) (hLK : L ≤ K)
    (hbudget : ∀ is : List (Fin d), is.length ≤ n →
      ∀ x, ‖euclideanCoordinateDerivList is c x‖ ≤ C is.length * L ^ is.length)
    (u : L2) (hu : MemFourierSobolev (n : ℝ) u)
    (hub : ∀ p, p ≤ n → fourierSobolevNorm (p : ℝ) u ≤ B p * A * K ^ p) :
    MemFourierSobolev (n : ℝ) (localizedScalarProduct c hc hcs u) ∧
      fourierSobolevNorm (n : ℝ) (localizedScalarProduct c hc hcs u) ≤
        (localizedMultiplierConstant d n *
          ∑ k ∈ Finset.range (n + 1), C (n - k) * B k) * A * K ^ n := by
  have hscaled : ∀ j, 0 ≤ C j * L ^ j :=
    fun j ↦ mul_nonneg (hC j) (pow_nonneg (by linarith) j)
  obtain ⟨hmem, hnorm⟩ := localizedScalarProduct_integer_bound n c hc hcs
    (fun j ↦ C j * L ^ j) hscaled hbudget u hu
  refine ⟨hmem, hnorm.trans ?_⟩
  calc
    _ ≤ localizedMultiplierConstant d n *
        ((∑ k ∈ Finset.range (n + 1), C (n - k) * B k) * A * K ^ n) :=
      mul_le_mul_of_nonneg_left (multiplier_sum_graded_le n C B hC hB hA hL hLK u hub)
        (localizedMultiplierConstant_pos d n).le
    _ = _ := by ring

/-- Fréchet derivative sup bounds imply the finite coordinate budgets used in
`app:ch_response:eq:response-reconstruction-grading`. This is the direct input
interface for the smooth compact coefficients of the reconstruction. -/
theorem localizedScalarProduct_frechet_bound (n : ℕ)
    (c : E → ℂ) (hc : ContDiff ℝ ∞ c) (hcs : HasCompactSupport c)
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hbudget : ∀ r, r ≤ n → ∀ x, ‖iteratedFDeriv ℝ r c x‖ ≤ C r)
    (u : L2) (hu : MemFourierSobolev (n : ℝ) u) :
    MemFourierSobolev (n : ℝ) (localizedScalarProduct c hc hcs u) ∧
      fourierSobolevNorm (n : ℝ) (localizedScalarProduct c hc hcs u) ≤
        localizedMultiplierConstant d n * mixedAmplitudeSobolevSum n C u :=
  localizedScalarProduct_integer_bound n c hc hcs C hC
    (fun is hi x ↦ (norm_euclideanCoordinateDerivList_le_iteratedFDeriv hc is x).trans
      (hbudget is.length hi x)) u hu

/-- Graded Fréchet budgets give the scalar estimate needed in
`app:ch_response:eq:response-graded-displacement` and its derivative and strain
variants, with no loss of coefficient derivative orders. -/
theorem localizedScalarProduct_frechet_graded_bound (n : ℕ)
    (c : E → ℂ) (hc : ContDiff ℝ ∞ c) (hcs : HasCompactSupport c)
    (C B : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (hB : ∀ j, 0 ≤ B j)
    {A L K : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L) (hLK : L ≤ K)
    (hbudget : ∀ r, r ≤ n → ∀ x, ‖iteratedFDeriv ℝ r c x‖ ≤ C r * L ^ r)
    (u : L2) (hu : MemFourierSobolev (n : ℝ) u)
    (hub : ∀ p, p ≤ n → fourierSobolevNorm (p : ℝ) u ≤ B p * A * K ^ p) :
    MemFourierSobolev (n : ℝ) (localizedScalarProduct c hc hcs u) ∧
      fourierSobolevNorm (n : ℝ) (localizedScalarProduct c hc hcs u) ≤
        (localizedMultiplierConstant d n *
          ∑ k ∈ Finset.range (n + 1), C (n - k) * B k) * A * K ^ n :=
  localizedScalarProduct_graded_bound n c hc hcs C B hC hB hA hL hLK
    (fun is hi x ↦ (norm_euclideanCoordinateDerivList_le_iteratedFDeriv hc is x).trans
      (hbudget is.length hi x)) u hu hub

/-- Real observation orders in
`app:ch_response:eq:response-graded-displacement`,
`app:ch_response:eq:response-graded-derivative`, and
`app:ch_response:eq:response-graded-strain` follow from any positive integer
budget `n ≥ s`. Interpolation retains the exact scale `K^s`, and only consumes
the Fréchet and envelope budgets through `n`. -/
theorem localizedScalarProduct_real_graded_bound (n : ℕ) (hn : 0 < n)
    {s : ℝ} (hs : 0 ≤ s) (hsn : s ≤ n)
    (c : E → ℂ) (hc : ContDiff ℝ ∞ c) (hcs : HasCompactSupport c)
    (C B : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (hB : ∀ j, 0 ≤ B j)
    {A L K : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L) (hLK : L ≤ K)
    (hbudget : ∀ r, r ≤ n → ∀ x, ‖iteratedFDeriv ℝ r c x‖ ≤ C r * L ^ r)
    (u : L2) (hu : MemFourierSobolev (n : ℝ) u)
    (hub : ∀ p, p ≤ n → fourierSobolevNorm (p : ℝ) u ≤ B p * A * K ^ p) :
    MemFourierSobolev s (localizedScalarProduct c hc hcs u) ∧
      fourierSobolevNorm s (localizedScalarProduct c hc hcs u) ≤
        (C 0 * B 0 + localizedMultiplierConstant d n *
          ∑ k ∈ Finset.range (n + 1), C (n - k) * B k) * A * K ^ s := by
  obtain ⟨hmem, hnorm⟩ := localizedScalarProduct_frechet_graded_bound n c hc hcs
    C B hC hB hA hL hLK hbudget u hu hub
  refine ⟨hmem.mono hsn, multiplier_interpolate_graded hn hs hsn (by linarith)
    (localizedScalarProduct c hc hcs u) hmem ?_ hnorm⟩
  have hzero := localizedScalarProduct_frechet_graded_bound 0 c hc hcs
    C B hC hB hA hL hLK (fun r hr ↦ hbudget r (by omega)) u
    (by simp) (fun p hp ↦ hub p (by omega))
  simpa [localizedMultiplierConstant] using hzero.2

end JanetCartan.IsometricEmbedding.Reconstruction
