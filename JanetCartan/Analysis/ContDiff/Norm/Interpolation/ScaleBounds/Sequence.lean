module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Interpolation from adjacent sequence estimates

The scalar finite-sequence step for `app:lem:elementary-interpolation-jets` in
paper.tex. An adjacent-order bound at every scale implies a two-endpoint bound
at arbitrary orders. The constant is uniform in both the sequence and the scale;
no monotonicity of the sequence is required.
-/

public section

namespace JanetCartan.CNormInterpolation

/-- Appendix B, `app:lem:elementary-interpolation-jets`: successive absorption
bounds an entry of a nonnegative sequence by its initial entry and an arbitrarily
small multiple of its next entry. The constant depends only on `C`, `n`, and `ε`. -/
theorem exists_sequence_absorption_bound {C : ℝ} (hC : 0 < C) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : ℕ → ℝ, (∀ i, 0 ≤ a i) →
      (∀ i, ∀ s : ℝ, 0 < s → s ≤ 1 →
        a (i + 1) ≤ C * (s⁻¹ * a i + s * a (i + 2))) →
      a n ≤ K * a 0 + ε * a (n + 1) := by
  induction n generalizing ε with
  | zero =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro a ha _
      simpa using (mul_nonneg hε.le (ha 1))
  | succ n ih =>
      let δ : ℝ := min 1 (ε / (2 * C))
      have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
      have hδ1 : δ ≤ 1 := min_le_left _ _
      have hδε : 2 * C * δ ≤ ε := by
        have h := min_le_right 1 (ε / (2 * C))
        have h' : δ * (2 * C) ≤ ε := (le_div_iff₀ (by positivity)).mp h
        nlinarith
      obtain ⟨K, hK, hbound⟩ := ih (ε := δ / (2 * C)) (by positivity)
      refine ⟨2 * C * δ⁻¹ * K, by positivity, ?_⟩
      intro a ha hadj
      have hprev := hbound a ha hadj
      have hnext := hadj n δ hδ hδ1
      -- The previous-order estimate contributes exactly half the next entry.
      have hprev' := mul_le_mul_of_nonneg_left hprev (show 0 ≤ C * δ⁻¹ by positivity)
      have hcancel : C * δ⁻¹ * (δ / (2 * C)) = 1 / 2 := by
        field_simp
      have hsmall := mul_le_mul_of_nonneg_right hδε (ha (n + 2))
      rw [mul_add, ← mul_assoc (C * δ⁻¹) (δ / (2 * C)), hcancel] at hprev'
      change a (n + 1) ≤ 2 * C * δ⁻¹ * K * a 0 + ε * a (n + 2)
      nlinarith

/-- Appendix B, `app:lem:elementary-interpolation-jets`: iterating the absorption
bound controls an entry by the two endpoints, with a constant independent of the
nonnegative sequence. -/
theorem exists_sequence_endpoint_bound {C : ℝ} (hC : 0 < C) (j d : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℕ → ℝ, (∀ i, 0 ≤ a i) →
      (∀ i, ∀ s : ℝ, 0 < s → s ≤ 1 →
        a (i + 1) ≤ C * (s⁻¹ * a i + s * a (i + 2))) →
      a j ≤ A * (a 0 + a (j + d)) := by
  induction d generalizing j with
  | zero =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro a ha _
      simpa using (ha 0)
  | succ d ih =>
      obtain ⟨K, hK, hstep⟩ := exists_sequence_absorption_bound hC j zero_lt_one
      obtain ⟨A, hA, hbound⟩ := ih (j + 1)
      refine ⟨K + A, add_pos hK hA, ?_⟩
      intro a ha hadj
      have hs := hstep a ha hadj
      have hb := hbound a ha hadj
      have hind : j + 1 + d = j + (d + 1) := by omega
      rw [hind] at hb
      have hn := mul_nonneg hK.le (ha (j + (d + 1)))
      nlinarith

/-- Appendix B, `app:lem:elementary-interpolation-jets`: adjacent-order scale
estimates imply the arbitrary-order two-term scale estimate. The positive constant
is chosen uniformly before the nonnegative sequence and the scale `0 < t ≤ 1`.
No monotonicity premise or smaller scale cutoff is needed. -/
theorem exists_sequence_scale_estimate {C : ℝ} (hC : 0 < C)
    {R j k : ℕ} (hRj : R < j) (hjk : j < k) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) →
      (∀ n, ∀ s : ℝ, 0 < s → s ≤ 1 →
        a (n + 1) ≤ C * (s⁻¹ * a n + s * a (n + 2))) →
      ∀ t : ℝ, 0 < t → t ≤ 1 →
        a j ≤ A * (t ^ ((R : ℝ) - j) * a R + t ^ ((k : ℝ) - j) * a k) := by
  obtain ⟨A, hA, hbound⟩ := exists_sequence_endpoint_bound hC (j - R) (k - j)
  refine ⟨A, hA, ?_⟩
  intro a ha hadj t ht ht1
  -- Normalize the orders relative to the lower endpoint.
  let b : ℕ → ℝ := fun n ↦ t ^ n * a (R + n)
  have hb : ∀ n, 0 ≤ b n := fun n ↦ mul_nonneg (pow_nonneg ht.le n) (ha _)
  have hb_adj : ∀ n, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      b (n + 1) ≤ C * (δ⁻¹ * b n + δ * b (n + 2)) := by
    intro n δ hδ hδ1
    have hδt : δ * t ≤ 1 := (mul_le_mul hδ1 ht1 ht.le zero_le_one).trans_eq (mul_one 1)
    have h := mul_le_mul_of_nonneg_left
      (hadj (R + n) (δ * t) (mul_pos hδ ht) hδt) (pow_nonneg ht.le (n + 1))
    change t ^ (n + 1) * a (R + (n + 1)) ≤ _
    calc
      t ^ (n + 1) * a (R + (n + 1)) ≤
          t ^ (n + 1) * (C * ((δ * t)⁻¹ * a (R + n) +
            (δ * t) * a (R + n + 2))) := by simpa [Nat.add_assoc] using h
      _ = C * (δ⁻¹ * b n + δ * b (n + 2)) := by
        dsimp [b]
        simp only [pow_succ, Nat.add_assoc]
        field_simp
  have h := hbound b hb hb_adj
  have hsum : j - R + (k - j) = k - R := by omega
  have hRj' : R + (j - R) = j := Nat.add_sub_of_le hRj.le
  have hRk : R + (k - R) = k := Nat.add_sub_of_le (hRj.trans hjk).le
  simp only [b, hsum, hRj', hRk, pow_zero, Nat.add_zero, one_mul] at h
  have hp₀ : t ^ (j - R) * t ^ ((R : ℝ) - j) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht, Nat.cast_sub hRj.le]
    rw [show (j : ℝ) - R + ((R : ℝ) - j) = 0 by ring, Real.rpow_zero]
  have hp₁ : t ^ (j - R) * t ^ ((k : ℝ) - j) = t ^ (k - R) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht,
      ← Real.rpow_natCast, Nat.cast_sub hRj.le, Nat.cast_sub (hRj.trans hjk).le]
    congr 1
    ring
  apply (mul_le_mul_iff_right₀ (pow_pos ht (j - R))).mp
  calc
    t ^ (j - R) * a j ≤ A * (a R + t ^ (k - R) * a k) := h
    _ = t ^ (j - R) *
        (A * (t ^ ((R : ℝ) - j) * a R + t ^ ((k : ℝ) - j) * a k)) := by
      calc
        _ = A * ((t ^ (j - R) * t ^ ((R : ℝ) - j)) * a R +
            (t ^ (j - R) * t ^ ((k : ℝ) - j)) * a k) := by rw [hp₀, hp₁, one_mul]
        _ = _ := by ring

end JanetCartan.CNormInterpolation
