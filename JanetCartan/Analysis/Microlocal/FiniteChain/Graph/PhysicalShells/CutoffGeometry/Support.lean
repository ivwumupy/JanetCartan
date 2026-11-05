module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Cutoffs

/-!
# Annular carriers of the fixed physical cutoffs

The comparable and noncomparable pair estimates for
`app:ch_regular:eq:chain-tail` use these bounds on the actual cutoffs from
`app:ch_regular:eq:joint-kernel-phase`. In particular the low annuli shrink
towards zero; there is no fixed lower frequency truncation.
-/

@[expose] public noncomputable section
open Set
namespace JanetCartan.FiniteChain.Graph.PhysicalShells
variable {n : ℕ}

/-- The expanding plateau in `app:ch_regular:eq:joint-kernel-phase`. -/
theorem expandingCutoff_eq_one (j : ℕ) {ξ : Euclidean n} (hξ : ‖ξ‖ ≤ (2 : ℝ) ^ j) :
    expandingCutoff j ξ = 1 := by
  apply (frequencyBump n).one_of_mem_closedBall
  change dist (((2 : ℝ) ^ j)⁻¹ • ξ) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
  exact (inv_mul_le_iff₀ (by positivity)).mpr (by simpa using hξ)

/-- The expanding carrier in `app:ch_regular:eq:joint-kernel-phase`. -/
theorem expandingCutoff_eq_zero (j : ℕ) {ξ : Euclidean n}
    (hξ : (2 : ℝ) ^ (j + 1) ≤ ‖ξ‖) : expandingCutoff j ξ = 0 := by
  apply (frequencyBump n).zero_of_le_dist
  change 2 ≤ dist (((2 : ℝ) ^ j)⁻¹ • ξ) 0
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
  exact (le_inv_mul_iff₀ (by positivity)).mpr (by simpa [pow_succ, mul_comm] using hξ)

/-- The contracting plateau in `app:ch_regular:eq:joint-kernel-phase`. -/
theorem contractingCutoff_eq_one (j : ℕ) {ξ : Euclidean n}
    (hξ : ‖ξ‖ ≤ ((2 : ℝ) ^ j)⁻¹) : contractingCutoff j ξ = 1 := by
  apply (frequencyBump n).one_of_mem_closedBall
  change dist ((2 : ℝ) ^ j • ξ) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_left hξ (by positivity : 0 ≤ (2 : ℝ) ^ j)
  simpa [ne_of_gt (by positivity : 0 < (2 : ℝ) ^ j)] using h

/-- The contracting carrier in `app:ch_regular:eq:joint-kernel-phase`. -/
theorem contractingCutoff_eq_zero (j : ℕ) {ξ : Euclidean n}
    (hξ : 2 * ((2 : ℝ) ^ j)⁻¹ ≤ ‖ξ‖) : contractingCutoff j ξ = 0 := by
  apply (frequencyBump n).zero_of_le_dist
  change 2 ≤ dist ((2 : ℝ) ^ j • ξ) 0
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_left hξ (by positivity : 0 ≤ (2 : ℝ) ^ j)
  simpa [← mul_assoc, mul_comm, mul_left_comm, ne_of_gt (by positivity : 0 < (2 : ℝ) ^ j)] using h

private theorem tsupport_subset_norm_interval {f : Euclidean n → ℝ} {a b : ℝ}
    (h : ∀ ξ, f ξ ≠ 0 → a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b) :
    tsupport f ⊆ {ξ | a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b} :=
  closure_minimal h ((isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const))

/-- The high graph annulus lies between `2^j` and `2^(j+2)`.
Consumer: the comparable/noncomparable split in `app:ch_regular:eq:chain-tail`. -/
theorem tsupport_highGraphCutoff_subset (j : ℕ) :
    tsupport (highGraphCutoff (n := n) j) ⊆
      {ξ | (2 : ℝ) ^ j ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (j + 2)} := by
  apply tsupport_subset_norm_interval
  intro ξ hξ
  constructor
  · by_contra! h
    apply hξ
    have h' : ‖ξ‖ ≤ (2 : ℝ) ^ (j + 1) :=
      h.le.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    simp [highGraphCutoff, expandingCutoff_eq_one j h.le, expandingCutoff_eq_one (j + 1) h']
  · by_contra! h
    apply hξ
    have h' : (2 : ℝ) ^ (j + 1) ≤ ‖ξ‖ :=
      (pow_le_pow_right₀ (by norm_num) (by omega)).trans h.le
    simp [highGraphCutoff, expandingCutoff_eq_zero j h', expandingCutoff_eq_zero (j + 1) h.le]

/-- The low graph annulus lies between `2^(-(j+1))` and `2^(1-j)`.
Consumer: summing all small graph frequencies in `app:ch_regular:eq:chain-tail`. -/
theorem tsupport_lowGraphCutoff_subset (j : ℕ) :
    tsupport (lowGraphCutoff (n := n) j) ⊆
      {ξ | ((2 : ℝ) ^ (j + 1))⁻¹ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * ((2 : ℝ) ^ j)⁻¹} := by
  have hi : ((2 : ℝ) ^ (j + 1))⁻¹ ≤ ((2 : ℝ) ^ j)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  apply tsupport_subset_norm_interval
  intro ξ hξ
  constructor
  · by_contra! h
    apply hξ
    simp [lowGraphCutoff, contractingCutoff_eq_one j (h.le.trans hi),
      contractingCutoff_eq_one (j + 1) h.le]
  · by_contra! h
    apply hξ
    simp [lowGraphCutoff, contractingCutoff_eq_zero j h.le,
      contractingCutoff_eq_zero (j + 1) ((mul_le_mul_of_nonneg_left hi (by norm_num)).trans h.le)]

/-- The zeroth output cutoff contains the bounded-frequency ball; its carrier
is still compact (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem tsupport_outputCutoff_zero_subset :
    tsupport (outputCutoff (n := n) 0) ⊆ Metric.closedBall 0 2 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro ξ hξ
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  exact hξ (expandingCutoff_eq_zero 0 (by simpa using h.le))

/-- The positive output indices are annuli, independently of the graph index
(`app:ch_regular:eq:chain-tail`). -/
theorem tsupport_outputCutoff_succ_subset (k : ℕ) :
    tsupport (outputCutoff (n := n) (k + 1)) ⊆
      {ξ | (2 : ℝ) ^ k ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (k + 2)} :=
  tsupport_highGraphCutoff_subset k

/-- Both halves of a graph regularizer avoid zero separately, as required
by phase extension for `app:ch_regular:eq:joint-kernel-phase`. -/
theorem zero_notMem_tsupport_highGraphCutoff (j : ℕ) :
    (0 : Euclidean n) ∉ tsupport (highGraphCutoff j) := by
  intro h
  have := (tsupport_highGraphCutoff_subset j h).1
  simp only [norm_zero] at this
  exact (by positivity : 0 < (2 : ℝ) ^ j).not_ge this

/-- The contracting graph carrier avoids zero without deleting a fixed ball
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem zero_notMem_tsupport_lowGraphCutoff (j : ℕ) :
    (0 : Euclidean n) ∉ tsupport (lowGraphCutoff j) := by
  intro h
  have := (tsupport_lowGraphCutoff_subset j h).1
  simp only [norm_zero] at this
  exact (by positivity : 0 < ((2 : ℝ) ^ (j + 1))⁻¹).not_ge this

end JanetCartan.FiniteChain.Graph.PhysicalShells
