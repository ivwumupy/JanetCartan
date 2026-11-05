module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Dyadic tail estimates from polynomial counting

The shell argument underlying the lattice sum in
`paper.tex`, Lemma `app:lem:sharp-fourier-embedding`.
-/

@[expose] public noncomputable section

namespace JanetCartan

private def dyadicIndex (x : ℝ) : ℕ :=
  (exists_nat_pow_near (le_max_left 1 x) (by norm_num : (1 : ℝ) < 2)).choose

private theorem dyadicIndex_spec {x : ℝ} (hx : 1 ≤ x) :
    (2 : ℝ) ^ dyadicIndex x ≤ x ∧ x < 2 ^ (dyadicIndex x + 1) := by
  have h := (exists_nat_pow_near (le_max_left 1 x)
    (by norm_num : (1 : ℝ) < 2)).choose_spec
  change (2 : ℝ) ^ dyadicIndex x ≤ max 1 x ∧
    max 1 x < 2 ^ (dyadicIndex x + 1) at h
  simpa only [max_eq_right hx] using h

/-- Finite-sum version of the dyadic shell argument in
`app:lem:sharp-fourier-embedding`. The counting hypothesis applies to arbitrary
finite subsets, so it does not presuppose summability of the tail. -/
theorem sum_rpow_tail_le_of_count {ι : Type*} (f : ι → ℝ) (n : ℕ)
    {C p : ℝ} (hC : 0 ≤ C) (hp : (n : ℝ) < p)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ s : Finset ι,
      (∀ i ∈ s, f i ≤ R) → (s.card : ℝ) ≤ C * R ^ n)
    {L : ℝ} (hL : 1 ≤ L) (s : Finset ι) (hs : ∀ i ∈ s, L < f i) :
    ∑ i ∈ s, (f i) ^ (-p) ≤
      (C * 2 ^ n / (1 - (2 : ℝ) ^ ((n : ℝ) - p))) * L ^ ((n : ℝ) - p) := by
  classical
  have hLpos : 0 < L := by linarith
  have hp0 : 0 ≤ p := (Nat.cast_nonneg n).trans hp.le
  let j : ι → ℕ := fun i ↦ dyadicIndex (f i / L)
  have hj (i : ι) (hi : i ∈ s) :
      (2 : ℝ) ^ j i * L ≤ f i ∧ f i ≤ 2 ^ (j i + 1) * L := by
    have h := dyadicIndex_spec ((le_div_iff₀ hLpos).mpr (by simpa using (hs i hi).le))
    exact ⟨(le_div_iff₀ hLpos).mp h.1, ((div_lt_iff₀ hLpos).mp h.2).le⟩
  let a : ℝ := C * 2 ^ n * L ^ ((n : ℝ) - p)
  let q : ℝ := (2 : ℝ) ^ ((n : ℝ) - p)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeom : Summable (fun m : ℕ ↦ a * q ^ m) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left a
  have hshell (m : ℕ) :
      ∑ i ∈ s.filter (fun i ↦ j i = m), (f i) ^ (-p) ≤ a * q ^ m := by
    have hupper (i : ι) (hi : i ∈ s.filter (fun i ↦ j i = m)) :
        f i ≤ (2 : ℝ) ^ (m + 1) * L := by
      have hi' := Finset.mem_filter.mp hi
      simpa only [hi'.2] using (hj i hi'.1).2
    have hr : 1 ≤ (2 : ℝ) ^ (m + 1) * L :=
      le_trans hL (le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num)))
    calc
      _ ≤ ∑ _i ∈ s.filter (fun i ↦ j i = m), ((2 : ℝ) ^ m * L) ^ (-p) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_filter.mp hi
        apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (neg_nonpos.mpr hp0)
        simpa only [hi'.2] using (hj i hi'.1).1
      _ = ((s.filter (fun i ↦ j i = m)).card : ℝ) * ((2 : ℝ) ^ m * L) ^ (-p) := by
        simp
      _ ≤ (C * ((2 : ℝ) ^ (m + 1) * L) ^ n) * ((2 : ℝ) ^ m * L) ^ (-p) := by
        gcongr
        exact hcount _ hr _ hupper
      _ = a * q ^ m := by
        dsimp [a, q]
        rw [pow_succ]
        simp only [mul_pow, Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 ^ m) hLpos.le,
          sub_eq_add_neg, Real.rpow_add hLpos,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
        rw [← Real.rpow_natCast_mul (by norm_num), mul_comm (m : ℝ),
          Real.rpow_mul_natCast (by norm_num)]
        ring

  calc
    _ = ∑ m ∈ s.image j, ∑ i ∈ s.filter (fun i ↦ j i = m), (f i) ^ (-p) :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi ↦ Finset.mem_image.mpr ⟨i, hi, rfl⟩) _).symm
    _ ≤ ∑ m ∈ s.image j, a * q ^ m := Finset.sum_le_sum fun m _ ↦ hshell m
    _ ≤ ∑' m : ℕ, a * q ^ m := hgeom.sum_le_tsum _ (fun _ _ ↦ mul_nonneg ha (pow_nonneg hq0 _))
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      dsimp [a, q]
      ring

end JanetCartan
