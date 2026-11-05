module

public import JanetCartan.Analysis.ContDiff.Norm.Defs

import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform bounds for dilated smooth functions

The analytic estimate in Proposition `main:prop:seed` of `paper.tex`, on an
arbitrary compact set. At order zero we use the mean-value theorem in the
parameter. At positive orders the chain rule supplies a factor `s^j`.
-/

@[expose] public noncomputable section

open scoped ContDiff
open Set

namespace JanetCartan

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Proposition `main:prop:seed`, estimate `main:eq:seed-small`: every spatial
jet of a smooth dilated function minus its value at zero is uniformly `O(s)`.
Compactness of `[0, 1] × K` gives constants independent of the dilation. -/
theorem exists_iteratedFDeriv_dilation_sub_const_bound {K : Set E} (hK : IsCompact K)
    {f : E → F} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (fun y ↦ f (s • y) - f 0) x‖ ≤ C * s := by
  have hcompact : IsCompact (Icc (0 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod hK
  have hsmul : Continuous (fun p : ℝ × E ↦ p.1 • p.2) :=
    continuous_fst.smul continuous_snd
  cases j with
  | zero =>
    have hcont : Continuous (fun p : ℝ × E ↦ fderiv ℝ f (p.1 • p.2) p.2) :=
      ((hf.continuous_fderiv (by simp)).comp hsmul).clm_apply continuous_snd
    obtain ⟨C, hC, hbound⟩ := (hcompact.image hcont).isBounded.exists_pos_norm_le
    refine ⟨C, hC, ?_⟩
    intro s hs x hx
    rw [norm_iteratedFDeriv_zero]
    have hderiv (t : ℝ) :
        HasDerivAt (fun u : ℝ ↦ f (u • x)) (fderiv ℝ f (t • x) x) t := by
      have hdx : HasDerivAt (fun u : ℝ ↦ u • x) x t := by
        simpa using (hasDerivAt_id t).smul_const x
      exact (hf.differentiable (by simp) (t • x)).hasFDerivAt.comp_hasDerivAt t hdx
    have hb : ∀ t ∈ Ico (0 : ℝ) 1, ‖fderiv ℝ f (t • x) x‖ ≤ C := by
      intro t ht
      exact hbound _ ⟨(t, x), ⟨Ico_subset_Icc_self ht, hx⟩, rfl⟩
    simpa using norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t _ ↦ (hderiv t).hasDerivWithinAt) hb s hs
  | succ j =>
    have hcont : Continuous (fun p : ℝ × E ↦ iteratedFDeriv ℝ (j + 1) f (p.1 • p.2)) :=
      (hf.continuous_iteratedFDeriv (by simp)).comp hsmul
    obtain ⟨C, hC, hbound⟩ := (hcompact.image hcont).isBounded.exists_pos_norm_le
    refine ⟨C, hC, ?_⟩
    intro s hs x hx
    have hfs : ContDiff ℝ (j + 1 : ℕ) (fun y ↦ f (s • y)) :=
      (hf.of_le (by simp)).comp (contDiff_const.smul contDiff_id)
    change ‖iteratedFDeriv ℝ (j + 1) ((fun y ↦ f (s • y)) - fun _ ↦ f 0) x‖ ≤ C * s
    rw [iteratedFDeriv_sub_apply hfs.contDiffAt contDiff_const.contDiffAt,
      iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero,
      iteratedFDeriv_comp_const_smul s (hf.of_le (by simp)), norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hs.1 _)]
    have hb : ‖iteratedFDeriv ℝ (j + 1) f (s • x)‖ ≤ C :=
      hbound _ ⟨(s, x), ⟨hs, hx⟩, rfl⟩
    have hp : s ^ (j + 1) ≤ s := by
      simpa [pow_succ] using mul_le_mul_of_nonneg_right (pow_le_one₀ hs.1 hs.2 (n := j)) hs.1
    calc
      s ^ (j + 1) * ‖iteratedFDeriv ℝ (j + 1) f (s • x)‖ ≤ s ^ (j + 1) * C :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg hs.1 _)
      _ ≤ s * C := mul_le_mul_of_nonneg_right hp hC.le
      _ = C * s := mul_comm _ _

/-- Proposition `main:prop:seed`, estimate `main:eq:seed-small`: summing the
uniform spatial jet bounds gives the compact-domain `C^r` estimate. -/
theorem exists_cNorm_dilation_sub_const_bound {K : Set E} (hK : IsCompact K)
    {f : E → F} (hf : ContDiff ℝ ∞ f) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Icc (0 : ℝ) 1,
      cNorm K r (fun y ↦ f (s • y) - f 0) ≤ C * s := by
  by_cases hne : K.Nonempty
  · choose C hC hbound using exists_iteratedFDeriv_dilation_sub_const_bound hK hf
    refine ⟨∑ j ∈ Finset.range (r + 1), C j,
      Finset.sum_pos (fun j _ ↦ hC j) ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ r)⟩, ?_⟩
    intro s hs
    unfold cNorm
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    apply csSup_le (hne.image _)
    rintro _ ⟨x, hx, rfl⟩
    exact hbound j s hs x hx
  · have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨1, zero_lt_one, ?_⟩
    intro s hs
    simpa [he, cNorm] using hs.1

end JanetCartan
