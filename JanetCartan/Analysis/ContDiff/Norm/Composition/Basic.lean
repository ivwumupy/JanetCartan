module

public import JanetCartan.Analysis.ContDiff.Norm.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Seminorm and partition estimates for composition

These helpers implement the chain-rule step of `app:lem:elementary-interpolation-jets`.
The real supremum in `cNorm` is used with explicit boundedness hypotheses.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.CompositionBounds

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `app:lem:elementary-interpolation-jets`: nonnegativity of the derivative seminorm. -/
theorem cNorm_nonneg (s : Set E) (r : ℕ) (f : E → F) : 0 ≤ cNorm s r f := by
  apply Finset.sum_nonneg
  intro j _
  exact Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact norm_nonneg _)

/-- `app:lem:elementary-interpolation-jets`: each bounded derivative is controlled by `cNorm`. -/
theorem norm_iteratedFDeriv_le_cNorm {s : Set E} {r j : ℕ} {f : E → F}
    (hb : BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' s))
    (hj : j ≤ r) {x : E} (hx : x ∈ s) : ‖iteratedFDeriv ℝ j f x‖ ≤ cNorm s r f := by
  apply (le_csSup hb ⟨x, hx, rfl⟩).trans
  apply Finset.single_le_sum _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  intro i _
  exact Real.sSup_nonneg (by rintro _ ⟨y, _, rfl⟩; exact norm_nonneg _)

/-- `app:lem:elementary-interpolation-jets`: compactness supplies bounded derivative images. -/
theorem bddAbove_derivative_image {s : Set E} (hs : IsCompact s) {r j : ℕ}
    {f : E → F} (hf : ContDiff ℝ r f) (hj : j ≤ r) :
    BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' s) :=
  hs.bddAbove_image ((hf.continuous_iteratedFDeriv (by exact_mod_cast hj)).norm.continuousOn)

/-- `app:lem:elementary-interpolation-jets`: summing uniform bounds controls `cNorm`,
including on the empty set. -/
theorem cNorm_le_sum {s : Set E} {r : ℕ} {f : E → F} {B : ℕ → ℝ}
    (hB : ∀ j ≤ r, 0 ≤ B j)
    (hf : ∀ j ≤ r, ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ B j) :
    cNorm s r f ≤ ∑ j ∈ Finset.range (r + 1), B j := by
  apply Finset.sum_le_sum
  intro j hj
  have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hB j hjr
  · exact csSup_le (hs.image _) (by rintro _ ⟨x, hx, rfl⟩; exact hf j hjr x hx)

/-- `app:lem:elementary-interpolation-jets`: pointwise Faà di Bruno norm estimate,
retaining the individual derivative orders of every factor. -/
theorem norm_iteratedFDeriv_comp_le_partition_sum {r n : ℕ} {f : E → F} {g : F → G}
    {x : E} (hg : ContDiffAt ℝ r g (f x)) (hf : ContDiffAt ℝ r f x) (hn : n ≤ r) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤
      ∑ p : OrderedFinpartition n, ‖iteratedFDeriv ℝ p.length g (f x)‖ *
        ∏ i, ‖iteratedFDeriv ℝ (p.partSize i) f x‖ := by
  rw [iteratedFDeriv_comp hg hf (by exact_mod_cast hn), FormalMultilinearSeries.taylorComp]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p _
  exact p.norm_compAlongOrderedFinpartition_le _ _

/-- `app:lem:elementary-interpolation-jets`: the derivative orders in a chain-rule term
sum to the differentiated order. -/
theorem sum_partSize {n : ℕ} (p : OrderedFinpartition n) : ∑ i, p.partSize i = n := by
  simpa using Fintype.card_congr p.equivSigma

/-- `app:eq:elementary-interpolation`: scalar seminorm interpolation, together with a
fixed low bound, yields the power majorants used in each Faà di Bruno term. The input
is the baseline-zero interpolation inequality, including its exact exponent. -/
theorem norm_iteratedFDeriv_le_rpow_of_cNorm_interpolation
    {s : Set E} (hs : IsCompact s) {k : ℕ} (hk : 0 < k) {f : E → F}
    (hf : ContDiff ℝ k f) {A M : ℝ} (hA : 1 ≤ A) (hM : cNorm s 0 f ≤ M)
    (hinterp : ∀ j, 0 < j → j < k →
      cNorm s j f ≤ A * (cNorm s 0 f) ^ (1 - (j : ℝ) / k) *
        (cNorm s k f) ^ ((j : ℝ) / k))
    {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {x : E} (hx : x ∈ s) :
    ‖iteratedFDeriv ℝ j f x‖ ≤
      (A * (1 + M)) * (1 + cNorm s k f) ^ ((j : ℝ) / k) := by
  have hM0 : 0 ≤ M := (cNorm_nonneg s 0 f).trans hM
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hlow : 1 ≤ 1 + M := by linarith
  have hhigh : 0 ≤ 1 + cNorm s k f := by linarith [cNorm_nonneg s k f]
  have hnorm := norm_iteratedFDeriv_le_cNorm (bddAbove_derivative_image hs hf hjk)
    (le_refl j) hx
  rcases lt_or_eq_of_le hjk with hjk | heq
  · apply hnorm.trans ((hinterp j hj hjk).trans _)
    have hθ0 : 0 ≤ (j : ℝ) / k := by positivity
    have hθ1 : (j : ℝ) / k ≤ 1 :=
      (div_le_one (by exact_mod_cast hk)).mpr (by exact_mod_cast hjk.le)
    have hpow : (cNorm s 0 f) ^ (1 - (j : ℝ) / k) ≤ 1 + M := by
      calc
        _ ≤ (1 + M) ^ (1 - (j : ℝ) / k) :=
          Real.rpow_le_rpow (cNorm_nonneg s 0 f) (by linarith) (by linarith)
        _ ≤ (1 + M) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlow (by linarith)
        _ = _ := Real.rpow_one _
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hA0)
      (Real.rpow_le_rpow (cNorm_nonneg s k f) (by linarith) hθ0)
      (Real.rpow_nonneg (cNorm_nonneg s k f) _) (mul_nonneg hA0 (by linarith))
  · subst j
    rw [div_self (by exact_mod_cast hk.ne'), Real.rpow_one]
    apply hnorm.trans
    calc
      cNorm s k f ≤ 1 + cNorm s k f := by linarith
      _ ≤ (A * (1 + M)) * (1 + cNorm s k f) :=
        le_mul_of_one_le_left hhigh (one_le_mul_of_one_le_of_one_le hA hlow)

/-- `app:eq:elementary-interpolation`: finitely many orderwise interpolation constants
can be replaced by a single constant, uniformly over the smooth function. -/
theorem exists_uniform_interpolation_constant (s : Set E) (k : ℕ)
    (hinterp : ∀ j, 0 < j → j < k → ∃ C : ℝ, 0 < C ∧
      ∀ f : E → F, ContDiff ℝ ∞ f →
        cNorm s j f ≤ C * (cNorm s 0 f) ^ (1 - (j : ℝ) / k) *
          (cNorm s k f) ^ ((j : ℝ) / k)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ f : E → F, ContDiff ℝ ∞ f →
      ∀ j, 0 < j → j < k →
        cNorm s j f ≤ A * (cNorm s 0 f) ^ (1 - (j : ℝ) / k) *
          (cNorm s k f) ^ ((j : ℝ) / k) := by
  have hconstants : ∀ j : Fin k, ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : E → F, ContDiff ℝ ∞ f → 0 < j.val →
        cNorm s j f ≤ C * (cNorm s 0 f) ^ (1 - (j.val : ℝ) / k) *
          (cNorm s k f) ^ ((j.val : ℝ) / k) := by
    intro j
    by_cases hj : 0 < j.val
    · obtain ⟨C, hC, h⟩ := hinterp j hj j.isLt
      exact ⟨C, hC.le, fun f hf _ ↦ h f hf⟩
    · exact ⟨0, le_rfl, fun _ _ h ↦ (hj h).elim⟩
  choose C hC hbound using hconstants
  refine ⟨1 + ∑ j, C j, ?_, ?_⟩
  · linarith [Finset.sum_nonneg (fun j _ ↦ hC j) (s := Finset.univ)]
  · intro f hf j hj hjk
    have hCj : C ⟨j, hjk⟩ ≤ 1 + ∑ i, C i := by
      have := Finset.single_le_sum (fun i _ ↦ hC i) (Finset.mem_univ ⟨j, hjk⟩)
      linarith
    apply (hbound ⟨j, hjk⟩ f hf hj).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCj (Real.rpow_nonneg (cNorm_nonneg s 0 f) _))
      (Real.rpow_nonneg (cNorm_nonneg s k f) _)

end JanetCartan.CompositionBounds
