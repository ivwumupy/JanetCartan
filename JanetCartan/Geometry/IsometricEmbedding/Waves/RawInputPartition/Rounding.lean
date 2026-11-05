module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.Scalar
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Literal rounding of continuous cutoffs to band labels

The source prefix in `app:ch_background:defn:bg-mixed` retains precisely the
bands with `κⱼ ≤ K`. No radial label is renamed. For `K ≥ 1` this has plateau
strictly larger than `K`, and outer radius at most `4K`. In particular the tail
can use the unchanged auxiliary cutoff at `K`, with plateau constant `c = 1`.
-/

@[expose] public noncomputable section

namespace JanetCartan.RawInputPartition

/-- Number of retained original band labels for the literal predicate `κⱼ ≤ K`
(`app:ch_background:defn:bg-mixed`). Only `K ≥ 1` is used by the recurrence. -/
def cutoffCount (K : ℝ) : ℕ :=
  if h : 1 ≤ K then (exists_nat_pow_near h (by norm_num : (1 : ℝ) < 2)).choose + 2 else 0

/-- The exact dyadic rounding interval (`app:ch_background:defn:bg-mixed`). -/
theorem cutoffCount_spec {K : ℝ} (hK : 1 ≤ K) :
    ∃ q : ℕ, cutoffCount K = q + 2 ∧ (2 : ℝ) ^ q ≤ K ∧ K < (2 : ℝ) ^ (q + 1) := by
  unfold cutoffCount
  rw [dite_eq_left hK]
  exact ⟨_, rfl, (exists_nat_pow_near hK (by norm_num : (1 : ℝ) < 2)).choose_spec⟩

/-- One-step scale formula used to compare the actual labels
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem dyadicScale_succ_eq_pow (q : ℕ) : dyadicScale (q + 1) = (2 : ℝ) ^ q := by
  simp [dyadicScale, pow_succ]

/-- Rounding retains exactly the source's predicate `κⱼ ≤ K`
(`app:ch_background:defn:bg-mixed`). -/
theorem lt_cutoffCount_iff {K : ℝ} (hK : 1 ≤ K) (j : ℕ) :
    j < cutoffCount K ↔ dyadicScale j ≤ K := by
  obtain ⟨q, hq, hlo, hhi⟩ := cutoffCount_spec hK
  rw [hq]
  constructor
  · intro hj
    exact (dyadicScale_strictMono.monotone (show j ≤ q + 1 by omega)).trans
      (by rwa [dyadicScale_succ_eq_pow])
  · intro hj
    by_contra h
    have he := dyadicScale_strictMono.monotone (show q + 2 ≤ j by omega)
    rw [show q + 2 = (q + 1) + 1 by omega, dyadicScale_succ_eq_pow] at he
    exact (hhi.trans_le (he.trans hj)).false

/-- The actual plateau radius lies in `(K, 2K]`; thus `c = 1` works uniformly
at all continuous recurrence cutoffs (`app:ch_background:defn:bg-mixed`). -/
theorem cutoffCount_plateau {K : ℝ} (hK : 1 ≤ K) :
    K < dyadicScale (cutoffCount K) ∧ dyadicScale (cutoffCount K) ≤ 2 * K := by
  obtain ⟨q, hq, hlo, hhi⟩ := cutoffCount_spec hK
  rw [hq, show q + 2 = (q + 1) + 1 by omega, dyadicScale_succ_eq_pow]
  exact ⟨hhi, by rw [pow_succ]; linarith⟩

/-- The original rounded prefix equals one below `K`
(`app:ch_background:defn:bg-mixed`). -/
theorem roundedPrefix_eq_one {K ρ : ℝ} (hK : 1 ≤ K) (hρ : ρ ≤ K) :
    scalarPrefix (cutoffCount K) ρ = 1 :=
  scalarPrefix_eq_one (hρ.trans (cutoffCount_plateau hK).1.le)

/-- The original rounded prefix vanishes at and above `4K`
(`app:ch_background:defn:bg-mixed`). -/
theorem roundedPrefix_eq_zero {K ρ : ℝ} (hK : 1 ≤ K) (hρ : 4 * K ≤ ρ) :
    scalarPrefix (cutoffCount K) ρ = 0 := by
  apply scalarPrefix_eq_zero
  linarith [(cutoffCount_plateau hK).2]

/-- Exact rounding at dyadic recurrence cutoffs: the retained labels are
`j < q + 2`, including the band with `κⱼ = K`
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem cutoffCount_two_pow (q : ℕ) : cutoffCount ((2 : ℝ) ^ q) = q + 2 := by
  obtain ⟨p, hp, hlo, hhi⟩ := cutoffCount_spec (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hpq : p ≤ q := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hlo
  have hqp : q < p + 1 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hhi
  have : p = q := by omega
  simpa [this] using hp

/-- For the literal cutoff `K = 2^q`, this normalization has plateau `2K`.
This documents the factor without renaming the sampled prefix
(`app:ch_background:defn:bg-mixed`). -/
theorem dyadic_cutoff_plateau (q : ℕ) :
    dyadicScale (cutoffCount ((2 : ℝ) ^ q)) = 2 * (2 : ℝ) ^ q := by
  rw [cutoffCount_two_pow, show q + 2 = (q + 1) + 1 by omega,
    dyadicScale_succ_eq_pow, pow_succ, mul_comm]

/-- Every band beyond the rounded cutoff vanishes below that cutoff
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem scalarBand_eq_zero_of_cutoffCount_le {K ρ : ℝ} (hK : 1 ≤ K)
    (hρ : ρ ≤ K) {j : ℕ} (hj : cutoffCount K ≤ j) : scalarBand j ρ = 0 := by
  apply scalarBand_eq_zero_of_le
  have hscale : K < dyadicScale j := lt_of_not_ge (fun h ↦
    (Nat.not_lt_of_ge hj) ((lt_cutoffCount_iff hK j).mpr h))
  exact hρ.trans hscale.le

/-- The actual fixed infinite square partition sums to one at every radius
in the floor-one high-pass. The proof reduces to an explicitly finite prefix
and proves that all later terms vanish (`app:ch_background:defn:bg-mixed`). -/
theorem tsum_scalarBand_sq_eq_one {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ∑' j : ℕ, scalarBand j ρ ^ 2 = 1 := by
  rw [tsum_eq_sum (s := Finset.range (cutoffCount ρ)) (fun j hj ↦ ?_)]
  · exact sum_scalarBand_sq_eq_one hρ (cutoffCount_plateau hρ).1.le
  · rw [scalarBand_eq_zero_of_cutoffCount_le hρ le_rfl
      (by simpa only [Finset.mem_range, not_lt] using hj), zero_pow (by decide)]

end JanetCartan.RawInputPartition
