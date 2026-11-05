module

public import JanetCartan.Analysis.ContDiff.Norm.Composition.Basic
public import JanetCartan.Analysis.ContDiff.Norm.Interpolation

/-!
# Finite-order composition estimates

For `app:lem:elementary-interpolation-jets`, Faà di Bruno gives a polynomial bound
in the actual `cNorm` of the inner map. The general tame estimates expose their
interpolation input. On positive-radius closed balls in finite-dimensional spaces,
`cNorm_le_interpolation_closedBall` discharges that input, giving a uniform bound
linear in the high norm, including order zero and any fixed finite derivative loss.
Smooth coefficient functions need only be controlled near the image of the
coordinate domain; the compact-range version also supplies the low norm bound.
The interpolation input comes directly from the constructive leaf theorem.
-/

@[expose] public noncomputable section

open scoped ContDiff
open JanetCartan.CompositionBounds

namespace JanetCartan

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `app:lem:elementary-interpolation-jets`: the number of chain-rule terms through order `r`.
This constant depends only on the differentiating order. -/
def compositionMultiplicity (r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (r + 1), (Fintype.card (OrderedFinpartition n) : ℝ)

/-- `app:lem:elementary-interpolation-jets`: composition with arbitrary nonnegative
majorants for each derivative of the inner and outer maps. -/
theorem cNorm_comp_le_partition_sum {s : Set E} {r : ℕ} {f : E → F} {g : F → G}
    (hf : ∀ x ∈ s, ContDiffAt ℝ r f x)
    (hg : ∀ x ∈ s, ContDiffAt ℝ r g (f x))
    {A B : ℕ → ℝ} (hA : ∀ j ≤ r, 0 ≤ A j) (hB : ∀ j ≤ r, 0 ≤ B j)
    (hfA : ∀ j, 1 ≤ j → j ≤ r → ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ A j)
    (hgB : ∀ j ≤ r, ∀ x ∈ s, ‖iteratedFDeriv ℝ j g (f x)‖ ≤ B j) :
    cNorm s r (g ∘ f) ≤ ∑ n ∈ Finset.range (r + 1),
      ∑ p : OrderedFinpartition n, B p.length * ∏ i, A (p.partSize i) := by
  apply cNorm_le_sum
  · intro n hn
    apply Finset.sum_nonneg
    intro p _
    exact mul_nonneg (hB _ (p.length_le.trans hn))
      (Finset.prod_nonneg (fun i _ ↦ hA _ ((p.partSize_le i).trans hn)))
  · intro n hn x hx
    apply (norm_iteratedFDeriv_comp_le_partition_sum (hg x hx) (hf x hx) hn).trans
    apply Finset.sum_le_sum
    intro p _
    apply mul_le_mul (hgB _ (p.length_le.trans hn) x hx)
      (Finset.prod_le_prod₀ (fun i _ ↦ norm_nonneg _) (fun i _ ↦
        hfA _ (p.partSize_pos i) ((p.partSize_le i).trans hn) x hx))
      (Finset.prod_nonneg (fun i _ ↦ norm_nonneg _)) (hB _ (p.length_le.trans hn))

/-- `app:lem:elementary-interpolation-jets`: a finite-order polynomial composition estimate.
The outer derivative bound is needed only along `f(s)`. -/
theorem cNorm_comp_le_polynomial {s : Set E} {r : ℕ} {f : E → F} {g : F → G}
    (hf : ∀ x ∈ s, ContDiffAt ℝ r f x)
    (hg : ∀ x ∈ s, ContDiffAt ℝ r g (f x))
    (hb : ∀ j ≤ r, BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' s))
    {C : ℝ} (hC : 0 ≤ C)
    (hgC : ∀ j ≤ r, ∀ x ∈ s, ‖iteratedFDeriv ℝ j g (f x)‖ ≤ C) :
    cNorm s r (g ∘ f) ≤
      compositionMultiplicity r * C * (1 + cNorm s r f) ^ r := by
  let D := 1 + cNorm s r f
  have hD : 1 ≤ D := by dsimp [D]; linarith [cNorm_nonneg s r f]
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  apply (cNorm_comp_le_partition_sum hf hg (A := fun _ ↦ D) (B := fun _ ↦ C)
    (fun _ _ ↦ hD0) (fun _ _ ↦ hC)
    (fun j _ hj x hx ↦ (norm_iteratedFDeriv_le_cNorm (hb j hj) hj hx).trans
      (by dsimp [D]; linarith)) hgC).trans
  calc
    _ ≤ ∑ n ∈ Finset.range (r + 1),
        ∑ _p : OrderedFinpartition n, C * D ^ r := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro p _
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hD (p.length_le.trans (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))) hC
    _ = _ := by simp [compositionMultiplicity, Finset.sum_mul, mul_assoc, D]

/-- `app:lem:elementary-interpolation-jets`: the polynomial estimate on compact sets,
expressed entirely using the two derivative seminorms. -/
theorem cNorm_comp_le_cNorm_polynomial {s : Set E} {t : Set F} (hs : IsCompact s)
    (ht : IsCompact t) {r : ℕ} {f : E → F} {g : F → G}
    (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) (hst : Set.MapsTo f s t) :
    cNorm s r (g ∘ f) ≤
      compositionMultiplicity r * cNorm t r g * (1 + cNorm s r f) ^ r := by
  apply cNorm_comp_le_polynomial (fun _ _ ↦ hf.contDiffAt) (fun _ _ ↦ hg.contDiffAt)
    (fun _ hj ↦ bddAbove_derivative_image hs hf hj) (cNorm_nonneg t r g)
  intro j hj x hx
  exact norm_iteratedFDeriv_le_cNorm (bddAbove_derivative_image ht hg hj) hj (hst hx)

/-- `app:lem:elementary-interpolation-jets`: the one-high composition bound from explicit
power interpolation estimates for the inner derivatives. The integer `k ≥ r` permits
a fixed finite loss; no interpolation theorem is asserted by this conditional result. -/
theorem cNorm_comp_le_tame_of_derivative_interpolation
    {s : Set E} {r k : ℕ} (hk : 0 < k) (hrk : r ≤ k) {f : E → F} {g : F → G}
    (hf : ∀ x ∈ s, ContDiffAt ℝ r f x)
    (hg : ∀ x ∈ s, ContDiffAt ℝ r g (f x))
    {A C H : ℝ} (hA : 1 ≤ A) (hC : 0 ≤ C) (hH : 1 ≤ H)
    (hinterp : ∀ j, 1 ≤ j → j ≤ r → ∀ x ∈ s,
      ‖iteratedFDeriv ℝ j f x‖ ≤ A * H ^ ((j : ℝ) / k))
    (hgC : ∀ j ≤ r, ∀ x ∈ s, ‖iteratedFDeriv ℝ j g (f x)‖ ≤ C) :
    cNorm s r (g ∘ f) ≤ compositionMultiplicity r * C * A ^ r * H := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  apply (cNorm_comp_le_partition_sum hf hg
    (A := fun j ↦ A * H ^ ((j : ℝ) / k)) (B := fun _ ↦ C)
    (fun _ _ ↦ mul_nonneg hA0 (Real.rpow_nonneg hH0.le _))
    (fun _ _ ↦ hC) hinterp hgC).trans
  calc
    _ ≤ ∑ n ∈ Finset.range (r + 1), ∑ _p : OrderedFinpartition n, C * (A ^ r * H) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnr : n ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ hC
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.rpow_sum_of_pos hH0, ← Finset.sum_div, ← Nat.cast_sum, sum_partSize]
      apply mul_le_mul (pow_le_pow_right₀ hA (p.length_le.trans hnr))
        _ (Real.rpow_nonneg hH0.le _) (pow_nonneg hA0 _)
      apply (Real.rpow_le_rpow_of_exponent_le hH _).trans_eq (Real.rpow_one H)
      exact (div_le_one (by exact_mod_cast hk)).mpr (by exact_mod_cast hnr.trans hrk)
    _ = _ := by simp [compositionMultiplicity, Finset.sum_mul, mul_assoc]

/-- `app:lem:elementary-interpolation-jets`: a one-high tame composition estimate with
finite loss `k - r`, conditional only on the stated baseline-zero scalar interpolation
inequalities. `M` bounds the low norm, and `A` is a common interpolation constant.
The derivative bounds on the coefficient function are required only on `f(s)`. -/
theorem cNorm_comp_le_tame_of_interpolation
    {s : Set E} (hs : IsCompact s) {r k : ℕ} (hk : 0 < k) (hrk : r ≤ k)
    {f : E → F} {g : F → G} (hf : ContDiff ℝ k f)
    (hg : ∀ x ∈ s, ContDiffAt ℝ r g (f x))
    {A C M : ℝ} (hA : 1 ≤ A) (hC : 0 ≤ C) (hM : cNorm s 0 f ≤ M)
    (hinterp : ∀ j, 0 < j → j < k →
      cNorm s j f ≤ A * (cNorm s 0 f) ^ (1 - (j : ℝ) / k) *
        (cNorm s k f) ^ ((j : ℝ) / k))
    (hgC : ∀ j ≤ r, ∀ x ∈ s, ‖iteratedFDeriv ℝ j g (f x)‖ ≤ C) :
    cNorm s r (g ∘ f) ≤
      compositionMultiplicity r * C * (A * (1 + M)) ^ r * (1 + cNorm s k f) := by
  have hM0 : 0 ≤ M := (cNorm_nonneg s 0 f).trans hM
  apply cNorm_comp_le_tame_of_derivative_interpolation hk hrk
    (fun _ _ ↦ (hf.of_le (by exact_mod_cast hrk)).contDiffAt) hg
    (one_le_mul_of_one_le_of_one_le hA (by linarith)) hC (by linarith [cNorm_nonneg s k f]) _ hgC
  intro j hj hjr x hx
  exact norm_iteratedFDeriv_le_rpow_of_cNorm_interpolation hs hk hf hA hM hinterp
    hj (hjr.trans hrk) hx

/-- `app:lem:elementary-interpolation-jets`: the tame bound for a smooth coefficient
function on a fixed compact range, with the scalar interpolation input left explicit. -/
theorem cNorm_comp_le_tame_on_compact_of_interpolation
    {s : Set E} {t : Set F} (hs : IsCompact s) (ht : IsCompact t)
    {r k : ℕ} (hk : 0 < k) (hrk : r ≤ k) {f : E → F} {g : F → G}
    (hf : ContDiff ℝ k f) (hg : ContDiff ℝ r g) (hst : Set.MapsTo f s t)
    {A M : ℝ} (hA : 1 ≤ A) (hM : cNorm s 0 f ≤ M)
    (hinterp : ∀ j, 0 < j → j < k →
      cNorm s j f ≤ A * (cNorm s 0 f) ^ (1 - (j : ℝ) / k) *
        (cNorm s k f) ^ ((j : ℝ) / k)) :
    cNorm s r (g ∘ f) ≤ compositionMultiplicity r * cNorm t r g *
      (A * (1 + M)) ^ r * (1 + cNorm s k f) := by
  apply cNorm_comp_le_tame_of_interpolation hs hk hrk hf (fun _ _ ↦ hg.contDiffAt)
    hA (cNorm_nonneg t r g) hM hinterp
  intro j hj x hx
  exact norm_iteratedFDeriv_le_cNorm (bddAbove_derivative_image ht hg hj) hj (hst hx)

/-- `app:lem:elementary-interpolation-jets`: a uniform one-high composition constant for
all smooth inner maps with a fixed low bound and compact range. The only additional
analytic input is the scalar interpolation theorem stated here, with constants
independent of the inner map. In particular this result does not assert that input. -/
theorem exists_cNorm_comp_le_tame_of_interpolation
    {s : Set E} {t : Set F} (hs : IsCompact s) (ht : IsCompact t)
    {r k : ℕ} (hk : 0 < k) (hrk : r ≤ k) {g : F → G} (hg : ContDiff ℝ r g)
    {M : ℝ} (hM : 0 ≤ M)
    (hinterp : ∀ j, 0 < j → j < k → ∃ C : ℝ, 0 < C ∧
      ∀ f : E → F, ContDiff ℝ ∞ f →
        cNorm s j f ≤ C * (cNorm s 0 f) ^ (1 - (j : ℝ) / k) *
          (cNorm s k f) ^ ((j : ℝ) / k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E → F, ContDiff ℝ ∞ f →
      Set.MapsTo f s t → cNorm s 0 f ≤ M →
        cNorm s r (g ∘ f) ≤ C * (1 + cNorm s k f) := by
  obtain ⟨A, hA, hinterpA⟩ := exists_uniform_interpolation_constant s k hinterp
  let D := compositionMultiplicity r * cNorm t r g * (A * (1 + M)) ^ r
  have hD : 0 ≤ D := by
    dsimp [D, compositionMultiplicity]
    exact mul_nonneg (mul_nonneg (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _))
      (cNorm_nonneg t r g)) (pow_nonneg (mul_nonneg (zero_le_one.trans hA) (by linarith)) _)
  refine ⟨1 + D, by linarith, ?_⟩
  intro f hf hst hfM
  apply (cNorm_comp_le_tame_on_compact_of_interpolation hs ht hk hrk
    (contDiff_infty.mp hf k) hg hst hA hfM (hinterpA f hf)).trans
  exact mul_le_mul_of_nonneg_right (show D ≤ 1 + D by linarith)
    (by linarith [cNorm_nonneg s k f])

/-- `app:lem:elementary-interpolation-jets`: a uniform one-high composition bound
on a positive-radius closed ball. The constant is independent of both maps and
of the outer derivative bound `B`. Only the values of the outer derivatives along
the image are used. Every `k ≥ r` is allowed, including `k = r = 0`.
The scalar interpolation input is discharged by `cNorm_le_interpolation_closedBall`. -/
theorem exists_cNorm_comp_le_tame_closedBall [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) {r k : ℕ} (hrk : r ≤ k)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : E → F, ContDiff ℝ ∞ f →
      cNorm (Metric.closedBall x ρ) 0 f ≤ M →
      ∀ (g : F → G) (B : ℝ), 0 ≤ B →
        (∀ y ∈ Metric.closedBall x ρ, ContDiffAt ℝ r g (f y)) →
        (∀ j ≤ r, ∀ y ∈ Metric.closedBall x ρ,
          ‖iteratedFDeriv ℝ j g (f y)‖ ≤ B) →
        cNorm (Metric.closedBall x ρ) r (g ∘ f) ≤
          K * B * (1 + cNorm (Metric.closedBall x ρ) k f) := by
  let s := Metric.closedBall x ρ
  by_cases hr : r = 0
  · subst r
    refine ⟨1, zero_lt_one, ?_⟩
    intro f _ _ g B hB _ hgB
    have hcomp : cNorm s 0 (g ∘ f) ≤ B := by
      refine (cNorm_le_sum (B := fun _ ↦ B) (fun _ _ ↦ hB) ?_).trans_eq ?_
      · intro j hj y hy
        have hj0 : j = 0 := by omega
        subst j
        simpa only [norm_iteratedFDeriv_zero, Function.comp_apply] using
          hgB 0 (le_refl 0) y hy
      · simp
    apply hcomp.trans
    simpa only [one_mul] using
      (le_mul_of_one_le_right hB (by linarith [cNorm_nonneg s k f]))
  have hk : 0 < k := lt_of_lt_of_le (Nat.pos_of_ne_zero hr) hrk
  have hinterp : ∀ j, 0 < j → j < k → ∃ C : ℝ, 0 < C ∧
      ∀ f : E → F, ContDiff ℝ ∞ f →
        cNorm s j f ≤ C * (cNorm s 0 f) ^ (1 - (j : ℝ) / k) *
          (cNorm s k f) ^ ((j : ℝ) / k) := by
    intro j hj hjk
    simpa only [Nat.cast_zero, sub_zero] using
      (cNorm_le_interpolation_closedBall (F := F) x hρ hj hjk)
  obtain ⟨A, hA, hinterpA⟩ := exists_uniform_interpolation_constant s k hinterp
  let D := compositionMultiplicity r * (A * (1 + M)) ^ r
  have hD : 0 ≤ D := by
    dsimp [D, compositionMultiplicity]
    exact mul_nonneg (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _))
      (pow_nonneg (mul_nonneg (zero_le_one.trans hA) (by linarith)) _)
  refine ⟨1 + D, by linarith, ?_⟩
  intro f hf hfM g B hB hg hgB
  calc
    _ ≤ compositionMultiplicity r * B * (A * (1 + M)) ^ r * (1 + cNorm s k f) :=
      cNorm_comp_le_tame_of_interpolation (isCompact_closedBall x ρ) hk hrk
        (contDiff_infty.mp hf k) hg hA hB hfM (hinterpA f hf) hgB
    _ = D * B * (1 + cNorm s k f) := by ring
    _ ≤ (1 + D) * B * (1 + cNorm s k f) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith [cNorm_nonneg s k f])
      exact mul_le_mul_of_nonneg_right (by linarith) hB

/-- `app:lem:elementary-interpolation-jets`: a fixed coefficient function smooth
near a compact range gives a uniform one-high estimate for all smooth inner maps
with that range and a fixed low bound. Taking `k = r` incurs no derivative loss;
taking `k = r + c` allows any fixed nonnegative loss. -/
theorem exists_cNorm_comp_le_tame_closedBall_on_compact [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) {t : Set F} (ht : IsCompact t)
    {r k : ℕ} (hrk : r ≤ k) {g : F → G}
    (hg : ∀ y ∈ t, ContDiffAt ℝ r g y) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E → F, ContDiff ℝ ∞ f →
      Set.MapsTo f (Metric.closedBall x ρ) t →
      cNorm (Metric.closedBall x ρ) 0 f ≤ M →
        cNorm (Metric.closedBall x ρ) r (g ∘ f) ≤
          C * (1 + cNorm (Metric.closedBall x ρ) k f) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_cNorm_comp_le_tame_closedBall (F := F) (G := G) x hρ hrk hM
  have hB := cNorm_nonneg t r g
  refine ⟨1 + K * cNorm t r g, by positivity, ?_⟩
  intro f hf hft hfM
  have hderiv : ∀ j ≤ r, ∀ y ∈ Metric.closedBall x ρ,
      ‖iteratedFDeriv ℝ j g (f y)‖ ≤ cNorm t r g := by
    intro j hj y hy
    apply norm_iteratedFDeriv_le_cNorm _ hj (hft hy)
    apply ht.bddAbove_image
    intro z hz
    exact ((hg z hz).continuousAt_iteratedFDeriv (by exact_mod_cast hj)).norm.continuousWithinAt
  apply (hbound f hf hfM g (cNorm t r g) hB (fun y hy ↦ hg (f y) (hft hy)) hderiv).trans
  exact mul_le_mul_of_nonneg_right (by linarith)
    (by linarith [cNorm_nonneg (Metric.closedBall x ρ) k f])

/-- `app:lem:elementary-interpolation-jets`: the compact low range itself supplies
the zeroth-order bound, so a fixed coefficient function smooth near that range
acts tamely on every smooth inner map into it. This includes the no-loss case
`k = r` and all fixed finite losses `k - r`. -/
theorem exists_cNorm_comp_le_tame_closedBall_of_compact_range [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) {t : Set F} (ht : IsCompact t)
    {r k : ℕ} (hrk : r ≤ k) {g : F → G}
    (hg : ∀ y ∈ t, ContDiffAt ℝ r g y) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E → F, ContDiff ℝ ∞ f →
      Set.MapsTo f (Metric.closedBall x ρ) t →
        cNorm (Metric.closedBall x ρ) r (g ∘ f) ≤
          C * (1 + cNorm (Metric.closedBall x ρ) k f) := by
  obtain ⟨M, hM⟩ := ht.bddAbove_image (continuous_norm.continuousOn)
  obtain ⟨C, hC, hbound⟩ := exists_cNorm_comp_le_tame_closedBall_on_compact
    x hρ ht hrk hg (le_max_left 0 M)
  refine ⟨C, hC, ?_⟩
  intro f hf hft
  apply hbound f hf hft
  have hlow := cNorm_le_sum (s := Metric.closedBall x ρ) (r := 0) (f := f)
    (B := fun _ ↦ max 0 M) (fun _ _ ↦ le_max_left 0 M) (by
      intro j hj y hy
      have hj0 : j = 0 := by omega
      subst j
      simpa only [norm_iteratedFDeriv_zero] using
        (hM ⟨f y, hft hy, rfl⟩).trans (le_max_right 0 M))
  simpa using hlow

end JanetCartan
