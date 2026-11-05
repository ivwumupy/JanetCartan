module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.Scalar

/-!
# Finite overlap of the normal-frequency annuli

The geometric counting step after `app:ch_waves:eq:sampling-operator-bounds`.
The inner and outer radii are fixed before the number of bands. This count is
consumed by the physical derivative estimate for the sum of full amplitudes.
-/

@[expose] public noncomputable section

namespace JanetCartan.Sampling.MeanNormalBound
open RawInputPartition

/-- At a fixed frequency, only a bounded number of the annuli
`α κⱼ ≤ ρ ≤ β κⱼ` can meet. The bound precedes both the band count and the
frequency (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_dyadic_annular_overlap_bound {α β : ℝ} (hα : 0 < α) :
    ∃ N : ℕ, 0 < N ∧ ∀ (J : ℕ) (ρ : ℝ),
      (Finset.univ.filter (fun j : Fin J ↦
        α * dyadicScale j.val ≤ ρ ∧ ρ ≤ β * dyadicScale j.val)).card ≤ N := by
  classical
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (β / α) (by norm_num : (1 : ℝ) < 2)
  let N := M + 1
  have hN : β < α * (2 : ℝ) ^ N := by
    have hpow : (2 : ℝ) ^ M ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (by omega)
    have hh := (div_lt_iff₀ hα).mp (hM.trans_le hpow)
    nlinarith
  have hsep (j k : ℕ) (hjk : j + N ≤ k) :
      β * dyadicScale j < α * dyadicScale k := by
    have hp : (2 : ℝ) ^ (j + N) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hjk
    have hs : dyadicScale (j + N) = (2 : ℝ) ^ N * dyadicScale j := by
      simp only [dyadicScale, pow_add]
      ring
    have hsc : dyadicScale (j + N) ≤ dyadicScale k := by
      dsimp [dyadicScale]
      exact div_le_div_of_nonneg_right hp (by norm_num)
    have hh := mul_lt_mul_of_pos_right hN (dyadicScale_pos j)
    rw [hs] at hsc
    nlinarith
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro J ρ
  let s := Finset.univ.filter (fun j : Fin J ↦
    α * dyadicScale j.val ≤ ρ ∧ ρ ≤ β * dyadicScale j.val)
  change s.card ≤ N
  by_cases hs : s.Nonempty
  · let k := s.min' hs
    have hk : k ∈ s := Finset.min'_mem s hs
    have hlo (j : s) : k.val ≤ j.val.val := by
      exact Finset.min'_le s j.val j.property
    have hhi (j : s) : j.val.val < k.val + N := by
      by_contra hj
      have he := hsep k.val j.val.val (by omega)
      have hkρ := (Finset.mem_filter.mp hk).2
      have hjρ := (Finset.mem_filter.mp j.property).2
      linarith
    let f : s → Fin N := fun j ↦ ⟨j.val.val - k.val, by have := hhi j; omega⟩
    have hf : Function.Injective f := by
      intro i j hij
      have he : i.val.val - k.val = j.val.val - k.val := congrArg Fin.val hij
      apply Subtype.ext
      apply Fin.ext
      have := hlo i
      have := hlo j
      omega
    have hc := Fintype.card_le_of_injective f hf
    simpa using hc
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

end JanetCartan.Sampling.MeanNormalBound
