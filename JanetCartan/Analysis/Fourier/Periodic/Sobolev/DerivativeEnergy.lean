module

public import JanetCartan.Analysis.Fourier.Periodic.Deriv
public import JanetCartan.Analysis.Fourier.Periodic.Parseval
public import JanetCartan.Analysis.Fourier.Periodic.Sobolev.Weights

/-!
# Coordinate derivative energies and Parseval

For Appendix A, `app:not:fourier` and `app:ch_regular_base:lem:ball-extension`,
we realize each Cartesian multiindex as an ordered list of coordinate derivatives.
The squared Fourier multiplier is the product of squared physical frequencies
`2π kᵢ`. Parseval then identifies its convergent series with the derivative's
squared L² norm. Summing over all multiindices through order `m` proves convergence
of the integer Bessel-potential series without a separate summability assumption.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan

variable {n : ℕ}

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The canonical Cartesian derivative list for a multiindex: coordinate `i` occurs
`α i` times, in increasing coordinate order (Appendix A, `app:not:fourier`). -/
def sobolevDerivativeList (α : Fin n → ℕ) : List (Fin n) :=
  (List.ofFn fun i : Fin n ↦ List.replicate (α i) i).flatten

/-- The list represents a derivative of total order `∑ i, α i`
(Appendix A, `app:not:fourier`). -/
theorem sobolevDerivativeList_length (α : Fin n → ℕ) :
    (sobolevDerivativeList α).length = ∑ i, α i := by
  simp [sobolevDerivativeList, List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def]

/-- Each coordinate is differentiated exactly its multiindex multiplicity
(Appendix A, `app:not:fourier`). -/
theorem sobolevDerivativeList_count (α : Fin n → ℕ) (i : Fin n) :
    (sobolevDerivativeList α).count i = α i := by
  simp [sobolevDerivativeList, List.count_flatten, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, List.count_replicate]

/-- The canonical derivative list has precisely the squared multiindex multiplier
in the unit-torus `2π` convention (Appendix A, `app:not:fourier`). -/
theorem sobolevDerivativeList_prod (α : Option (Fin n) → ℕ) (k : Fin n → ℤ) :
    ((sobolevDerivativeList (fun i ↦ α (some i))).map (fun i ↦ (2 * Real.pi * (k i : ℝ)) ^ 2)).prod =
      sobolevMonomial α k := by
  simp [sobolevDerivativeList, List.map_flatten, List.prod_flatten, List.map_ofFn,
    sobolevMonomial, Function.comp_def, List.prod_ofFn]

/-- One coordinate derivative multiplies the energy of the real Fourier pair by
`(2π kᵢ)²` (Appendix A, `app:not:fourier`). -/
theorem sq_periodicFourierCoeff_coordinateDeriv [CompleteSpace F]
    {f : Torus n → F} (hf : IsSmoothPeriodic f) (i : Fin n) (k : Fin n → ℤ) :
    ‖(periodicFourierCoeff (periodicCoordinateDeriv i f) k).1‖ ^ 2 +
      ‖(periodicFourierCoeff (periodicCoordinateDeriv i f) k).2‖ ^ 2 =
    (2 * Real.pi * (k i : ℝ)) ^ 2 *
      (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2) := by
  rw [periodicFourierCoeff_coordinateDeriv_smul hf]
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, mul_pow, sq_abs]
  ring

/-- An ordered list of Cartesian derivatives multiplies the Fourier energy by
the product of its squared symbols (Appendix A, `app:not:fourier`). -/
theorem sq_periodicFourierCoeff_coordinateDerivList [CompleteSpace F]
    {f : Torus n → F} (hf : IsSmoothPeriodic f) (is : List (Fin n)) (k : Fin n → ℤ) :
    ‖(periodicFourierCoeff (periodicCoordinateDerivList is f) k).1‖ ^ 2 +
      ‖(periodicFourierCoeff (periodicCoordinateDerivList is f) k).2‖ ^ 2 =
    (is.map (fun i ↦ (2 * Real.pi * (k i : ℝ)) ^ 2)).prod *
      (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2) := by
  induction is with
  | nil => simp [periodicCoordinateDerivList]
  | cons i is ih =>
    rw [periodicCoordinateDerivList,
      sq_periodicFourierCoeff_coordinateDeriv (hf.coordinateDerivList is), ih]
    simp only [List.map_cons, List.prod_cons, mul_assoc]

/-- The Cartesian multiindex derivative, implemented by repeated actual coordinate
derivatives in canonical order (Appendix A, `app:not:fourier`). -/
def periodicMultiindexDeriv (α : Fin n → ℕ) (f : Torus n → F) : Torus n → F :=
  periodicCoordinateDerivList (sobolevDerivativeList α) f

/-- Cartesian multiindex derivatives preserve smooth periodicity
(Appendix A, `app:not:fourier`). -/
theorem IsSmoothPeriodic.multiindexDeriv {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (α : Fin n → ℕ) :
    IsSmoothPeriodic (periodicMultiindexDeriv α f) :=
  hf.coordinateDerivList _

/-- The squared Fourier multiplier of a Cartesian multiindex derivative
(Appendix A, `app:not:fourier`). The slack coordinate is unused. -/
theorem sq_periodicFourierCoeff_multiindexDeriv [CompleteSpace F]
    {f : Torus n → F} (hf : IsSmoothPeriodic f) (α : Option (Fin n) → ℕ) (k : Fin n → ℤ) :
    ‖(periodicFourierCoeff (periodicMultiindexDeriv (fun i ↦ α (some i)) f) k).1‖ ^ 2 +
      ‖(periodicFourierCoeff (periodicMultiindexDeriv (fun i ↦ α (some i)) f) k).2‖ ^ 2 =
    sobolevMonomial α k *
      (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2) := by
  rw [periodicMultiindexDeriv, sq_periodicFourierCoeff_coordinateDerivList hf,
    sobolevDerivativeList_prod]

/-- The manuscript's integer Sobolev norm: the L² norm of all Cartesian derivatives
through order `m` (Appendix A, `app:not:fourier`;
`app:ch_regular_base:lem:ball-extension`). Each multiindex occurs once, as witnessed
by `sobolevMultiindexEquiv`; its `none` coordinate records the unused degree. -/
def periodicDerivativeL2Norm (m : ℕ) (f : Torus n → F) : ℝ :=
  Real.sqrt (∑ α ∈ sobolevMultiindices n m,
    periodicL2Norm (periodicMultiindexDeriv (fun i ↦ α (some i)) f) ^ 2)

end Normed

section InnerProduct
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Parseval for a Cartesian multiindex derivative, including convergence of
the weighted Fourier series (Appendix A, `app:not:fourier`). -/
theorem IsSmoothPeriodic.hasSum_sobolevMonomial {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (α : Option (Fin n) → ℕ) :
    HasSum (fun k : Fin n → ℤ ↦ sobolevMonomial α k *
      (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2))
      (periodicL2Norm (periodicMultiindexDeriv (fun i ↦ α (some i)) f) ^ 2) := by
  exact (hf.multiindexDeriv _).hasSum_sq_periodicFourierCoeff.congr_fun
    (fun k ↦ (sq_periodicFourierCoeff_multiindexDeriv hf α k).symm)

/-- The convergent Fourier series for the sum of all derivative energies through
order `m` (Appendix A, `app:ch_regular_base:lem:ball-extension`). -/
theorem IsSmoothPeriodic.hasSum_sobolevDerivativeWeight {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (m : ℕ) :
    HasSum (fun k : Fin n → ℤ ↦ sobolevDerivativeWeight m k *
      (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2))
      (∑ α ∈ sobolevMultiindices n m,
        periodicL2Norm (periodicMultiindexDeriv (fun i ↦ α (some i)) f) ^ 2) := by
  simpa only [sobolevDerivativeWeight, Finset.sum_mul] using
    hasSum_sum (s := sobolevMultiindices n m) (fun α _ ↦ hf.hasSum_sobolevMonomial α)

/-- Every smooth periodic field with finite-dimensional real Hilbert codomain has
a summable Fourier Sobolev series at every nonnegative integer order. This follows
from derivative Parseval, without an additional decay or summability hypothesis
(Appendix A, `app:not:fourier`; `app:ch_regular_base:lem:ball-extension`). -/
theorem IsSmoothPeriodic.summable_periodicSobolevNorm {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (m : ℕ) :
    Summable (fun k : Fin n → ℤ ↦ (1 + frequencyNorm k ^ 2) ^ (m : ℝ) *
      (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2)) := by
  simp only [Real.rpow_natCast]
  exact (summable_sobolevDerivativeWeight_iff m _
    (fun k ↦ add_nonneg (sq_nonneg _) (sq_nonneg _))).mp
      (hf.hasSum_sobolevDerivativeWeight m).summable

end InnerProduct
end JanetCartan
