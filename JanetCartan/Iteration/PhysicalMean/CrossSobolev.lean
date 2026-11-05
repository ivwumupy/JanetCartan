module

public import JanetCartan.Iteration.PhysicalMean.CrossAmplitude
public import JanetCartan.Analysis.Sobolev.Local.Cutoff.Product
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Lossless-order source Sobolev control of the modified mean amplitude

The sharp amplitude test uses `H^ell`, not `C^ell`, in its source-dependent
factor. Here the full corrected coefficient and the original measurement
keep their finite physical `C^ell` budgets, while the SAME canonical
background is integrated in L² without Sobolev embedding
(`app:ch_mean_pairs:eq:mean-quadratic-low`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open CanonicalRowComparison

/-- Physical L² jets of the literal modified cross amplitude, with NO extra
source derivatives. `B` is the same individual canonical field (or its lower
balanced derivative); `G` is the full corrected amplitude (or its higher
forward template). Only genuine coefficient factors enter the suprema. -/
theorem crossAmplitude_jet_L2_bound {n N : ℕ}
    {K : Set (Euclidean n)} (hK : IsCompact K) (s : ℕ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B G : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hC : ContDiff ℝ ∞ C) (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G)
    (hGK : tsupport G ⊆ K)
    (hBmem : ∀ j ≤ s, MemLp (iteratedFDeriv ℝ j B) 2 volume) :
    let H := fun x ↦ complexCrossMeasurement (C x) (B x) (G x)
    MemLp (iteratedFDeriv ℝ s H) 2 volume ∧
      lpNorm (iteratedFDeriv ℝ s H) 2 volume ≤
        (2 * ((2 : ℝ) ^ s) ^ 2) * cNorm K s C * cNorm K s G *
          ∑ j ∈ Finset.range (s + 1), lpNorm (iteratedFDeriv ℝ j B) 2 volume := by
  intro H
  have hH : ContDiff ℝ ∞ H := (complexCrossMeasurement_cNorm_bound hK s C B G hC hB hG).1
  have hHK : tsupport H ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    apply hGK
    apply subset_tsupport
    intro hz
    exact hx (by simp only [H, hz, map_zero])
  have hHjK : tsupport (iteratedFDeriv ℝ s H) ⊆ K :=
    (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) s).trans hHK
  let F := fun x ↦ ∑ j ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ j B x‖
  have hFnonneg (x) : 0 ≤ F x := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hFeq : F = ∑ j ∈ Finset.range (s + 1), (fun x ↦ ‖iteratedFDeriv ℝ j B x‖) := by
    funext x
    simp only [F, Finset.sum_apply]
  have hF : MemLp F 2 volume := by
    rw [hFeq]
    exact memLp_finsetSum' (Finset.range (s + 1)) (fun j hj ↦
      (hBmem j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).norm)
  let P := (2 * ((2 : ℝ) ^ s) ^ 2) * cNorm K s C * cNorm K s G
  have hP : 0 ≤ P := mul_nonneg
    (mul_nonneg (by positivity) (cNorm_nonneg K s C)) (cNorm_nonneg K s G)
  have hbound (x) : ‖iteratedFDeriv ℝ s H x‖ ≤ P * ‖F x‖ := by
    by_cases hx : x ∈ K
    · rw [Real.norm_of_nonneg (hFnonneg x)]
      exact norm_iteratedFDeriv_complexCrossMeasurement_le_source_jets hK s C B G hC hB hG hx
    · rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hHjK ht)), norm_zero]
      exact mul_nonneg hP (norm_nonneg _)
  have hjmeas : AEStronglyMeasurable (iteratedFDeriv ℝ s H) volume :=
    (hH.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
  have hjmem : MemLp (iteratedFDeriv ℝ s H) 2 volume :=
    hF.of_le_mul hjmeas (Filter.Eventually.of_forall hbound)
  have hFnorm : lpNorm F 2 volume ≤
      ∑ j ∈ Finset.range (s + 1), lpNorm (iteratedFDeriv ℝ j B) 2 volume := by
    calc
      _ ≤ ∑ j ∈ Finset.range (s + 1),
          lpNorm (fun x ↦ ‖iteratedFDeriv ℝ j B x‖) 2 volume := by
        rw [hFeq]
        exact lpNorm_sum_le (s := Finset.range (s + 1)) (fun j hj ↦
          (hBmem j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).norm) (by norm_num)
      _ = _ := Finset.sum_congr rfl fun j hj ↦
        lpNorm_norm (hBmem j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).aestronglyMeasurable 2
  refine ⟨hjmem, ?_⟩
  have hh := LocalSobolev.eLpNorm_toReal_le_mul_of_bound hjmeas hF hP hbound
  simp only [toReal_eLpNorm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hFnorm hP)

end JanetCartan.PhysicalMean
