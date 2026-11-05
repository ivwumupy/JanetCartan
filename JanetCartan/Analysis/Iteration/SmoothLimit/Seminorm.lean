module

public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Seminorm convergence from uniform derivative convergence

The `C^r` convergence assertion following `main:eq:final-Cr` in Section 9.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology
open Filter

namespace JanetCartan

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Section 9 after `main:eq:final-Cr`: uniform convergence of all derivatives
through order `r` implies convergence in the manuscript's `C^r` seminorm on the
same open set. Compactness is unnecessary because convergence is uniform. -/
theorem tendsto_cNorm_sub_of_uniform_derivatives {M : ℕ → E → F} {f : E → F} {W : Set E} {r : ℕ}
    (hW : IsOpen W) (hM : ∀ J, ContDiffOn ℝ r (M J) W) (hf : ContDiffOn ℝ r f W)
    (hconv : ∀ i ≤ r, TendstoUniformlyOn (fun J ↦ iteratedFDeriv ℝ i (M J))
      (iteratedFDeriv ℝ i f) atTop W) :
    Tendsto (fun J ↦ cNorm W r (M J - f)) atTop (𝓝 0) := by
  have hsup (i : ℕ) (hi : i ≤ r) :
      Tendsto (fun J ↦ sSup ((fun x ↦ ‖iteratedFDeriv ℝ i (M J - f) x‖) '' W))
        atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨J, hJ⟩ := eventually_atTop.1
      (Metric.tendstoUniformlyOn_iff.1 (hconv i hi) (ε / 2) (half_pos hε))
    refine ⟨J, fun K hK ↦ ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (sSup_norm_iteratedFDeriv_nonneg W i (M K - f))]
    apply lt_of_le_of_lt ?_ (half_lt_self hε)
    apply Real.sSup_le _ (half_pos hε).le
    rintro _ ⟨x, hx, rfl⟩
    change ‖iteratedFDeriv ℝ i (M K - f) x‖ ≤ ε / 2
    rw [iteratedFDeriv_sub_apply (i := i)
      (((hM K).contDiffAt (hW.mem_nhds hx)).of_le (by exact_mod_cast hi))
      ((hf.contDiffAt (hW.mem_nhds hx)).of_le (by exact_mod_cast hi))]
    simpa only [dist_eq_norm, norm_sub_rev] using (hJ K hK x hx).le
  simpa only [cNorm, Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.range (r + 1)) (fun i hi ↦
      hsup i (Nat.le_of_lt_succ (Finset.mem_range.1 hi)))

end JanetCartan
