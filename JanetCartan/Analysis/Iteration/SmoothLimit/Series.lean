module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# One smooth sum with eventual derivative bounds

The smooth-series argument of Section 9 (`main:eq:final-Cr`). The tail may
start at a different index for each derivative order; the limit and domain do not change.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology
open Filter

namespace JanetCartan

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Section 9, `main:eq:final-Cr`: differentiation of a series with eventual,
order-dependent summable bounds. The finitely many exceptions need no uniform bounds. -/
theorem iteratedFDeriv_tsum_eventually {f : ℕ → E → F} {v : ℕ → ℕ → ℝ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hv : ∀ r, Summable (v r))
    (hb : ∀ r, ∀ᶠ j in atTop, ∀ x, ‖iteratedFDeriv ℝ r (f j) x‖ ≤ v r j)
    (r : ℕ) :
    iteratedFDeriv ℝ r (fun x ↦ ∑' j, f j x) =
      fun x ↦ ∑' j, iteratedFDeriv ℝ r (f j) x := by
  classical
  have he : ∀ᶠ j in atTop, ∀ k ∈ Finset.range (r + 1),
      ∀ x, ‖iteratedFDeriv ℝ k (f j) x‖ ≤ v k j := by
    rw [eventually_all_finset]
    exact fun k _ ↦ hb k
  obtain ⟨J, hJ⟩ := eventually_atTop.1 he
  let T := Finset.range J
  have htail : ∀ k : ℕ, k ≤ r → ∀ j : {j // j ∉ T}, ∀ x,
      ‖iteratedFDeriv ℝ k (f j) x‖ ≤ v k j := by
    intro k hk j x
    exact hJ j (by simpa [T] using j.property) k (by simpa using hk) x
  have hs (x : E) : Summable (fun j ↦ f j x) := by
    apply Summable.of_norm_bounded_eventually (hv 0)
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hb 0] with j hj
    simpa only [norm_iteratedFDeriv_zero] using hj x
  have hd (x : E) : Summable (fun j ↦ iteratedFDeriv ℝ r (f j) x) := by
    apply Summable.of_norm_bounded_eventually (hv r)
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hb r] with j hj
    exact hj x
  have hsplit : (fun x ↦ ∑' j, f j x) =
      (fun x ↦ ∑ j ∈ T, f j x) + (fun x ↦ ∑' j : {j // j ∉ T}, f j x) := by
    funext x
    exact ((hs x).sum_add_tsum_subtype_compl T).symm
  have htailSmooth : ContDiff ℝ (r : ℕ∞) (fun x ↦ ∑' j : {j // j ∉ T}, f j x) := by
    apply contDiff_tsum (fun j : {j // j ∉ T} ↦ (hf j).of_le (by simp))
      (fun k _ ↦ (hv k).subtype _)
    intro k j x hk
    exact htail k (by exact_mod_cast hk) j x
  rw [hsplit, iteratedFDeriv_add (ContDiff.sum (fun j _ ↦ (hf j).of_le (by simp)))
    htailSmooth]
  funext x
  rw [Pi.add_apply, iteratedFDeriv_fun_sum_apply
    (fun j _ ↦ ((hf j).of_le (by simp)).contDiffAt)]
  rw [iteratedFDeriv_tsum (N := (r : ℕ∞))
    (fun j : {j // j ∉ T} ↦ (hf j).of_le (by simp)) (fun k _ ↦ (hv k).subtype _)
    (fun k j x hk ↦ htail k (by exact_mod_cast hk) j x) le_rfl]
  exact (hd x).sum_add_tsum_subtype_compl T

/-- Section 9, `main:eq:final-Cr`: the same pointwise sum is smooth at every order. -/
theorem contDiff_tsum_eventually {f : ℕ → E → F} {v : ℕ → ℕ → ℝ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hv : ∀ r, Summable (v r))
    (hb : ∀ r, ∀ᶠ j in atTop, ∀ x, ‖iteratedFDeriv ℝ r (f j) x‖ ≤ v r j) :
    ContDiff ℝ ∞ (fun x ↦ ∑' j, f j x) := by
  exact contDiff_tsum_of_eventually hf (fun r _ ↦ hv r)
    (fun r _ ↦ Nat.cofinite_eq_atTop.symm ▸ hb r)

/-- Section 9, `main:eq:final-Cr`: partial sums converge uniformly at every derivative
order to the derivatives of one sum, on the same entire coordinate domain. -/
theorem tendstoUniformly_iteratedFDeriv_sum {f : ℕ → E → F} {v : ℕ → ℕ → ℝ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hv : ∀ r, Summable (v r))
    (hb : ∀ r, ∀ᶠ j in atTop, ∀ x, ‖iteratedFDeriv ℝ r (f j) x‖ ≤ v r j)
    (r : ℕ) :
    TendstoUniformly (fun J ↦ iteratedFDeriv ℝ r (fun x ↦ ∑ j ∈ Finset.range J, f j x))
      (iteratedFDeriv ℝ r (fun x ↦ ∑' j, f j x)) atTop := by
  rw [iteratedFDeriv_tsum_eventually hf hv hb]
  have heq (J : ℕ) : iteratedFDeriv ℝ r (fun x ↦ ∑ j ∈ Finset.range J, f j x) =
      fun x ↦ ∑ j ∈ Finset.range J, iteratedFDeriv ℝ r (f j) x := by
    funext x
    exact iteratedFDeriv_fun_sum_apply (fun j _ ↦ ((hf j).of_le (by simp)).contDiffAt)
  simp_rw [heq]
  rw [← tendstoUniformlyOn_univ]
  exact tendstoUniformlyOn_tsum_nat_eventually (hv r)
    ((hb r).mono (fun _ hj x _ ↦ hj x))

/-- Section 9, `main:eq:final-Cr`: adding the fixed smooth reference gives one smooth
limit, with uniform convergence of all derivatives on the same domain.
The summable eventual derivative bounds are the analytic input. -/
theorem smooth_limit_of_eventual_bounds {G : E → F} {f : ℕ → E → F}
    {v : ℕ → ℕ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hv : ∀ r, Summable (v r))
    (hb : ∀ r, ∀ᶠ j in atTop, ∀ x, ‖iteratedFDeriv ℝ r (f j) x‖ ≤ v r j) :
    ContDiff ℝ ∞ (fun x ↦ G x + ∑' j, f j x) ∧
      ∀ r : ℕ, TendstoUniformly
        (fun J ↦ iteratedFDeriv ℝ r (fun x ↦ G x + ∑ j ∈ Finset.range J, f j x))
        (iteratedFDeriv ℝ r (fun x ↦ G x + ∑' j, f j x)) atTop := by
  have hs := contDiff_tsum_eventually hf hv hb
  refine ⟨hG.add hs, fun r ↦ ?_⟩
  have hp (J : ℕ) : ContDiff ℝ (r : ℕ) (fun x ↦ ∑ j ∈ Finset.range J, f j x) :=
    ContDiff.sum (fun j _ ↦ (hf j).of_le (by simp))
  simp_rw [fun_iteratedFDeriv_add (hG.of_le (by simp)) (hp _),
    fun_iteratedFDeriv_add (hG.of_le (by simp)) (hs.of_le (by simp))]
  rw [Metric.tendstoUniformly_iff] at *
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.1
    (tendstoUniformly_iteratedFDeriv_sum hf hv hb r) ε hε] with J hJ
  intro x
  simpa only [Pi.add_apply, dist_add_left] using hJ x

/-- Section 9, `main:eq:final-Cr`: a reference map smooth only on the fixed open
neighborhood suffices. All derivative orders converge on that same neighborhood. -/
theorem smooth_limit_on_of_eventual_bounds {G : E → F} {f : ℕ → E → F}
    {v : ℕ → ℕ → ℝ} {W : Set E} (hW : IsOpen W) (hG : ContDiffOn ℝ ∞ G W)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hv : ∀ r, Summable (v r))
    (hb : ∀ r, ∀ᶠ j in atTop, ∀ x, ‖iteratedFDeriv ℝ r (f j) x‖ ≤ v r j) :
    ContDiffOn ℝ ∞ (fun x ↦ G x + ∑' j, f j x) W ∧
      ∀ r : ℕ, TendstoUniformlyOn
        (fun J ↦ iteratedFDeriv ℝ r (fun x ↦ G x + ∑ j ∈ Finset.range J, f j x))
        (iteratedFDeriv ℝ r (fun x ↦ G x + ∑' j, f j x)) atTop W := by
  have hs := contDiff_tsum_eventually hf hv hb
  refine ⟨hG.add hs.contDiffOn, fun r ↦ ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.1
    (tendstoUniformly_iteratedFDeriv_sum hf hv hb r) ε hε] with J hJ
  intro x hx
  have hGx : ContDiffAt ℝ r G x := (hG.contDiffAt (hW.mem_nhds hx)).of_le (by simp)
  have hp : ContDiff ℝ r (fun x ↦ ∑ j ∈ Finset.range J, f j x) :=
    ContDiff.sum (fun j _ ↦ (hf j).of_le (by simp))
  rw [fun_iteratedFDeriv_add_apply hGx hp.contDiffAt,
    fun_iteratedFDeriv_add_apply hGx (hs.of_le (by simp)).contDiffAt, dist_add_left]
  exact hJ x

end JanetCartan
