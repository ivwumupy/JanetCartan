module

public import JanetCartan.Analysis.Fourier.Periodic
public import JanetCartan.Analysis.Fourier.Periodic.Lattice.Dyadic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Pi

/-!
# Counting physical Fourier frequencies

Integer frequencies on the unit torus carry the physical factor `2 * π`.
The estimates here supply the lattice bounds used in
`paper.tex`, Lemma `app:lem:sharp-fourier-embedding`.
-/

@[expose] public noncomputable section

namespace JanetCartan

variable {n : ℕ}

/-- Nonnegativity of the physical frequency used in
`app:lem:sharp-fourier-embedding`. -/
theorem frequencyNorm_nonneg (k : Fin n → ℤ) : 0 ≤ frequencyNorm k := by
  unfold frequencyNorm
  positivity

/-- Each integer coordinate is bounded by the physical frequency
(`app:lem:sharp-fourier-embedding`, unit-torus convention). -/
theorem abs_coordinate_le_frequencyNorm (k : Fin n → ℤ) (i : Fin n) :
    |(k i : ℝ)| ≤ frequencyNorm k := by
  have h := PiLp.norm_apply_le
    (WithLp.toLp 2 (fun i ↦ (k i : ℝ)) : EuclideanSpace ℝ (Fin n)) i
  simp only [Real.norm_eq_abs] at h
  exact h.trans (le_mul_of_one_le_left (norm_nonneg _) (by
    have := Real.two_le_pi
    linarith))

/-- Coordinate box containing the physical frequency ball of
`app:lem:sharp-fourier-embedding`. -/
def frequencyBox (n : ℕ) (L : ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ ↦ Finset.Icc (-(⌈L⌉₊ : ℤ)) (⌈L⌉₊ : ℤ)

private theorem mem_frequencyBox {k : Fin n → ℤ} {L : ℝ}
    (h : frequencyNorm k ≤ L) : k ∈ frequencyBox n L := by
  simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc, ← abs_le]
  intro i
  exact_mod_cast (abs_coordinate_le_frequencyNorm k i).trans (h.trans (Nat.le_ceil L))

/-- The finite ball of physical frequencies, including its boundary
(`app:lem:sharp-fourier-embedding`). -/
def frequencyBall (n : ℕ) (L : ℝ) : Finset (Fin n → ℤ) :=
  (frequencyBox n L).filter fun k ↦ frequencyNorm k ≤ L

/-- Membership in the finite frequency ball of
`app:lem:sharp-fourier-embedding`. -/
@[simp] theorem mem_frequencyBall {k : Fin n → ℤ} {L : ℝ} :
    k ∈ frequencyBall n L ↔ frequencyNorm k ≤ L := by
  simp only [frequencyBall, Finset.mem_filter]
  exact ⟨And.right, fun h ↦ ⟨mem_frequencyBox h, h⟩⟩

/-- Bounded physical frequencies form a finite set, in every dimension,
as used in `app:lem:sharp-fourier-embedding`. -/
theorem finite_frequencyNorm_le (n : ℕ) (L : ℝ) :
    {k : Fin n → ℤ | frequencyNorm k ≤ L}.Finite := by
  exact (frequencyBall n L).finite_toSet.subset (by
    intro k hk
    exact mem_frequencyBall.mpr hk)

/-- Explicit `O(L^n)` lattice count, uniform for `L ≥ 1`, supplying the
low-frequency bound in `app:lem:sharp-fourier-embedding`. -/
theorem card_frequencyBall_le {L : ℝ} (hL : 1 ≤ L) :
    ((frequencyBall n L).card : ℝ) ≤ 5 ^ n * L ^ n := by
  have hcard : (frequencyBox n L).card = (2 * ⌈L⌉₊ + 1) ^ n := by
    have hc : (Finset.Icc (-(⌈L⌉₊ : ℤ)) (⌈L⌉₊ : ℤ)).card = 2 * ⌈L⌉₊ + 1 := by
      rw [Int.card_Icc]
      omega
    simp [frequencyBox, Fintype.card_piFinset, hc]
  calc
    ((frequencyBall n L).card : ℝ) ≤ (frequencyBox n L).card := by
      exact_mod_cast Finset.card_filter_le (frequencyBox n L) _
    _ = (2 * (⌈L⌉₊ : ℝ) + 1) ^ n := by rw [hcard]; push_cast; rfl
    _ ≤ (5 * L) ^ n := by
      gcongr
      have := Nat.ceil_lt_add_one (show 0 ≤ L by linarith)
      linarith
    _ = 5 ^ n * L ^ n := mul_pow _ _ _

/-- A constant independent of the cutoff for the lattice tail estimate in
`app:lem:sharp-fourier-embedding`. It is positive whenever `p > n`. -/
def frequencyTailConstant (n : ℕ) (p : ℝ) : ℝ :=
  5 ^ n * 2 ^ n / (1 - (2 : ℝ) ^ ((n : ℝ) - p))

/-- Positivity of the tail constant in `app:lem:sharp-fourier-embedding`. -/
theorem frequencyTailConstant_pos {p : ℝ} (hp : (n : ℝ) < p) :
    0 < frequencyTailConstant n p := by
  have h : (2 : ℝ) ^ ((n : ℝ) - p) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold frequencyTailConstant
  positivity

/-- Polynomial decay for any finite collection of frequencies above `L`,
as required in `app:lem:sharp-fourier-embedding`. -/
theorem sum_frequencyNorm_rpow_tail_le {p L : ℝ} (hp : (n : ℝ) < p)
    (hL : 1 ≤ L) (s : Finset (Fin n → ℤ)) (hs : ∀ k ∈ s, L < frequencyNorm k) :
    ∑ k ∈ s, frequencyNorm k ^ (-p) ≤
      frequencyTailConstant n p * L ^ ((n : ℝ) - p) := by
  apply sum_rpow_tail_le_of_count frequencyNorm n (by positivity) hp _ hL s hs
  intro R hR t ht
  have hsub : t ⊆ frequencyBall n R := fun k hk ↦ mem_frequencyBall.mpr (ht k hk)
  exact (show (t.card : ℝ) ≤ (frequencyBall n R).card by
    exact_mod_cast Finset.card_le_card hsub).trans (card_frequencyBall_le hR)

private theorem sum_frequencyNorm_rpow_indicator_le {p L : ℝ} (hp : (n : ℝ) < p)
    (hL : 1 ≤ L) (s : Finset (Fin n → ℤ)) :
    ∑ k ∈ s, (if L < frequencyNorm k then frequencyNorm k ^ (-p) else 0) ≤
      frequencyTailConstant n p * L ^ ((n : ℝ) - p) := by
  classical
  rw [← Finset.sum_filter]
  exact sum_frequencyNorm_rpow_tail_le hp hL _ fun _ hk ↦ (Finset.mem_filter.mp hk).2

/-- Summability of the physical-frequency tail for every real `p > n`
(`app:lem:sharp-fourier-embedding`). This justifies the real-valued infinite sum. -/
theorem summable_frequencyNorm_rpow_tail {p L : ℝ} (hp : (n : ℝ) < p) (hL : 1 ≤ L) :
    Summable (fun k : Fin n → ℤ ↦
      if L < frequencyNorm k then frequencyNorm k ^ (-p) else 0) := by
  apply summable_of_sum_le _ (sum_frequencyNorm_rpow_indicator_le hp hL)
  intro k
  change 0 ≤ if L < frequencyNorm k then frequencyNorm k ^ (-p) else 0
  split_ifs
  · exact Real.rpow_nonneg (frequencyNorm_nonneg k) _
  · exact le_rfl

/-- The lattice tail is at most `C(n,p) L^(n-p)`, uniformly for `L ≥ 1`.
This is the high-frequency squared-weight estimate in
`app:lem:sharp-fourier-embedding`. -/
theorem tsum_frequencyNorm_rpow_tail_le {p L : ℝ} (hp : (n : ℝ) < p) (hL : 1 ≤ L) :
    (∑' k : Fin n → ℤ, if L < frequencyNorm k then frequencyNorm k ^ (-p) else 0) ≤
      frequencyTailConstant n p * L ^ ((n : ℝ) - p) :=
  (summable_frequencyNorm_rpow_tail hp hL).tsum_le_of_sum_le
    (sum_frequencyNorm_rpow_indicator_le hp hL)

/-- Subtype form of tail summability in `app:lem:sharp-fourier-embedding`. -/
theorem summable_frequencyNorm_rpow_subtype {p L : ℝ} (hp : (n : ℝ) < p) (hL : 1 ≤ L) :
    Summable (fun k : {k : Fin n → ℤ // L < frequencyNorm k} ↦
      frequencyNorm k.val ^ (-p)) := by
  have h := (summable_frequencyNorm_rpow_tail hp hL).subtype
    (fun k ↦ L < frequencyNorm k)
  exact h.congr fun k ↦ ite_eq_left k.property

/-- Subtype form of the polynomial lattice tail bound in
`app:lem:sharp-fourier-embedding`. -/
theorem tsum_frequencyNorm_rpow_subtype_le {p L : ℝ} (hp : (n : ℝ) < p) (hL : 1 ≤ L) :
    (∑' k : {k : Fin n → ℤ // L < frequencyNorm k}, frequencyNorm k.val ^ (-p)) ≤
      frequencyTailConstant n p * L ^ ((n : ℝ) - p) := by
  calc
    _ = ∑' k : Fin n → ℤ, {k : Fin n → ℤ | L < frequencyNorm k}.indicator
        (fun k ↦ frequencyNorm k ^ (-p)) k :=
      tsum_subtype _ _
    _ = ∑' k : Fin n → ℤ, if L < frequencyNorm k then frequencyNorm k ^ (-p) else 0 := by
      apply tsum_congr
      intro k
      rw [Set.indicator_apply]
      rfl
    _ ≤ _ := tsum_frequencyNorm_rpow_tail_le hp hL

/-- The full lattice power sum converges for `p > n`, with `0^(-p) = 0`
as in Lean's real-power convention (`app:lem:sharp-fourier-embedding`). -/
theorem summable_frequencyNorm_rpow {p : ℝ} (hp : (n : ℝ) < p) :
    Summable (fun k : Fin n → ℤ ↦ frequencyNorm k ^ (-p)) := by
  apply (finite_frequencyNorm_le n 1).summable_compl_iff.mp
  rw [summable_subtype_iff_indicator]
  exact (summable_frequencyNorm_rpow_tail hp (L := 1) le_rfl).congr fun k ↦ by
    simp only [Set.indicator_apply, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]

end JanetCartan
