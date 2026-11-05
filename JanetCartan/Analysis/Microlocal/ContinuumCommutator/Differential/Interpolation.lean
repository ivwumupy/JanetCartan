module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Terms
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.TameZero

/-!
# First-derivative baseline and joint interpolation

The scalar quantitative step of `app:ch_background:eq:bg-commutator`. The low
primitive budget is `μ + 1`, with `μ = 2 * (d + 1)`, and the high budget is
`μ + s`. Thus the shift is independent of `s`. Normal reduction must supply
these primitive bounds from the geometric and initial-scalar profiles.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- `app:ch_background:eq:bg-commutator`: interpolation of the primitive
coefficient profile from the fixed first-derivative baseline, including order
one. `K` is chosen before the amplitude and its high bound. -/
theorem exists_commutator_geometric_budget (d n : ℕ) (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ),
        (∀ ξ, ContDiff ℝ ∞ (b ξ)) → ∀ H : ℝ,
        HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) M →
        HasAmplitudeDerivativeBound b (2 * (d + 1) + (n + 1)) H →
        ∀ j, j ≤ n → HasAmplitudeDerivativeBound b (2 * (d + 1) + 1 + j)
          (K * (max 1 H) ^ ((j : ℝ) / n)) := by
  by_cases hn : n = 0
  · subst n
    refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro b _ H hM _ j hj
    have hj0 : j = 0 := by omega
    subst j
    intro ξ is his z
    simpa using (hM ξ is (by simpa using his) z).trans (le_max_right 1 M)
  · obtain ⟨K, hK, hi⟩ := exists_physicalAmplitude_geometric_budget d
      (2 * (d + 1) + 1) n (Nat.pos_of_ne_zero hn) M
    refine ⟨K, hK, ?_⟩
    intro b hb H hM hH
    exact hi b hb H hM (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hH)

/-- `app:ch_background:eq:bg-commutator`: the actual derivative amplitude
in a surviving branch has the required low L² budget. The exponent counts only
physical derivatives beyond the first one; source derivatives are included. -/
theorem commutator_transfer_geometric_bound
    (n : ℕ) (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (K H : ℝ)
    (hbudget : ∀ j, j ≤ n → HasAmplitudeDerivativeBound b (2 * (d + 1) + 1 + j)
      (K * (max 1 H) ^ ((j : ℝ) / n)))
    (is : List (Fin d)) (hlen : is.length = n + 1)
    (p : List (Fin d) × List (Fin d)) (hp : p ∈ differentialCommutatorTerms is) :
    HasAmplitudeDerivativeBound (iteratedTransferAmplitude b p.1) (2 * (d + 1))
      (2 ^ p.1.length * (K * (max 1 H) ^ (((p.1.length - 1 : ℕ) : ℝ) / n))) := by
  have hspec := differentialCommutatorTerms_spec is p hp
  apply hasAmplitudeDerivativeBound_iteratedTransferAmplitude b hb
  have hi := hbudget (p.1.length - 1) (by omega)
  simpa only [show 2 * (d + 1) + 1 + (p.1.length - 1) =
    2 * (d + 1) + p.1.length by omega] using hi

/-- `app:ch_background:eq:bg-commutator`: joint coefficient/datum
interpolation. The high bound multiplies only L², including the `s = 1`
endpoint. The input is a genuine Fourier Sobolev datum, not a list of norms. -/
theorem commutator_geometric_weight_mul_sobolev_le
    (n r k : ℕ) (hr : 0 < r) (hcount : r + k = n + 1)
    (H : ℝ) (f : L²) (hf : MemFourierSobolev (n : ℝ) f) :
    (max 1 H) ^ (((r - 1 : ℕ) : ℝ) / n) * fourierSobolevNorm (k : ℝ) f ≤
      fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖ := by
  have hk : k ≤ n := by omega
  have he : (((r - 1 : ℕ) : ℝ) / n) ≤ 1 - (k : ℝ) / n := by
    by_cases hn : n = 0
    · subst n; simp
    · have hsum : (r - 1 : ℕ) + k = n := by omega
      have hsum' : ((r - 1 : ℕ) : ℝ) + k = n := by exact_mod_cast hsum
      apply le_of_eq
      apply (div_eq_iff (by exact_mod_cast hn : (n : ℝ) ≠ 0)).mpr
      field_simp
      linarith
  calc
    _ ≤ (max 1 H) ^ (1 - (k : ℝ) / n) * fourierSobolevNorm (k : ℝ) f :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) he)
        (fourierSobolevNorm_nonneg _ _)
    _ ≤ _ := by
      simpa only [fourierSobolevNorm_zero, add_comm] using
        fourierSobolevNorm_weighted_interpolate (by positivity)
          (show (k : ℝ) ≤ n by exact_mod_cast hk) (show 0 ≤ max 1 H by positivity) hf

/-- `app:ch_background:eq:bg-commutator`: the `2π` cost of the actual ordered
compact-test derivatives, used to estimate each surviving branch. -/
theorem fourierSobolevNorm_coordinateDerivList_toLp_le
    (is : List (Fin d)) (n : ℕ) (u : E → ℂ)
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    fourierSobolevNorm (n : ℝ)
      (((contDiff_euclideanCoordinateDerivList hu is).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_euclideanCoordinateDerivList hus is)).toLp
          (euclideanCoordinateDerivList is u)) ≤
      (2 * Real.pi) ^ is.length * fourierSobolevNorm ((n + is.length : ℕ) : ℝ)
        ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u) := by
  induction is generalizing n with
  | nil => simp [euclideanCoordinateDerivList]
  | cons i is ih =>
    have h := HasEuclideanL2CoordinateDerivative.fourierSobolevNorm_le
      (show (0 : ℝ) ≤ n by positivity)
      (hasEuclideanL2CoordinateDerivative_toLp (euclideanCoordinateDerivList is u)
        (contDiff_euclideanCoordinateDerivList hu is)
        (hasCompactSupport_euclideanCoordinateDerivList hus is) i)
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        (memFourierSobolev_nat_toLp (n + 1) (euclideanCoordinateDerivList is u)
          (contDiff_euclideanCoordinateDerivList hu is)
          (hasCompactSupport_euclideanCoordinateDerivList hus is)))
    have hi := mul_le_mul_of_nonneg_left (ih (n + 1)) (show 0 ≤ 2 * Real.pi by positivity)
    have he := h.trans (by simpa only [Nat.cast_add, Nat.cast_one] using hi)
    convert he using 1 <;>
      simp [euclideanCoordinateDerivList, List.length_cons, pow_succ,
        add_comm, add_left_comm, mul_assoc, mul_comm]

end JanetCartan.Pseudodifferential
