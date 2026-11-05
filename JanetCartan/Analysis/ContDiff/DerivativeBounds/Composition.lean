module

public import JanetCartan.Analysis.ContDiff.DerivativeBounds.Algebra
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Composition preserves the stated derivative reserve

Faà di Bruno is applied with the allocated order of each derivative. A fixed
smooth outer operation preserves every natural reserve. When both maps vary,
reserve at least one pays for the outer derivative as well. The constants
are the original finite partition sums and do not depend on the scale.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff BigOperators

namespace JanetCartan.DerivativeBounds
open ResponseTransfer.GradedPrimitives

variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Composition of two varying profiles has the SAME reserve, provided it
is at least one. The outer derivative order is included in the budget
(`app:ch_regular_base:lem:buffered-interpolation`, composition clause). -/
theorem norm_jet_comp_graded_le {f : X → E} {g : E → F} {x : X} {N k R : ℕ}
    (hf : ContDiffAt ℝ N f x) (hg : ContDiffAt ℝ N g (f x)) (hk : k ≤ N)
    (A B : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    {T : ℝ} (hT : 1 ≤ T) (hR : 1 ≤ R)
    (hgjet : ∀ j ≤ k, ‖iteratedFDeriv ℝ j g (f x)‖ ≤ A j * T ^ (j - R))
    (hfjet : ∀ j, 1 ≤ j → j ≤ k →
      ‖iteratedFDeriv ℝ j f x‖ ≤ B j * T ^ (j - R)) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ compositionConstant A B k * T ^ (k - R) := by
  apply (CompositionBounds.norm_iteratedFDeriv_comp_le_partition_sum hg hf hk).trans
  rw [compositionConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  have hp : (∏ i, ‖iteratedFDeriv ℝ (p.partSize i) f x‖) ≤
      ∏ i, (B (p.partSize i) * T ^ (p.partSize i - R)) :=
    Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      (fun i _ ↦ hfjet _ (p.partSize_pos i) (p.partSize_le i))
  calc
    _ ≤ (A p.length * T ^ (p.length - R)) *
        ∏ i, (B (p.partSize i) * T ^ (p.partSize i - R)) :=
      mul_le_mul (hgjet _ p.length_le) hp
        (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
        (mul_nonneg (hA _) (pow_nonneg (zero_le_one.trans hT) _))
    _ = (A p.length * ∏ i, B (p.partSize i)) *
        T ^ ((p.length - R) + ∑ i, (p.partSize i - R)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hT (partition_composition_reserve_le p hR))
      (mul_nonneg (hA _) (Finset.prod_nonneg fun _ _ ↦ hB _))

/-- A fixed smooth operation with bounded derivatives along the original
range preserves the full `C^r` profile, including order zero and reserve zero.
The outer derivative bounds are fixed coefficients, not estimates on the
composed function (`app:lem:elementary-interpolation-jets`). -/
theorem hasDerivativeProfile_fixed_smooth_comp
    {K : Set X} (hK : IsCompact K) {f : X → E} {g : E → F}
    (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x)
    (hg : ∀ x ∈ K, ContDiffAt ℝ ∞ g (f x))
    (A B : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    {T : ℝ} (hT : 1 ≤ T) (R : ℕ)
    (hprofile : HasDerivativeProfile K f R T B)
    (hcoeff : ∀ j x, x ∈ K → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ A j) :
    HasDerivativeProfile K (g ∘ f) R T
      (fun r ↦ ∑ j ∈ Finset.range (r + 1), compositionConstant A B j) := by
  intro r
  have hjet (j : ℕ) (x : X) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ compositionConstant A B j * T ^ (j - R) := by
    apply norm_jet_comp_fixed_outer_le
      ((hf x hx).of_le (by simp : (j : ℕ∞ω) ≤ ∞))
      ((hg x hx).of_le (by simp : (j : ℕ∞ω) ≤ ∞)) le_rfl A B hA hB hT R
      (fun q _ ↦ hcoeff q x hx)
    intro q _ _
    exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hf y hy).of_le (by simp : (q : ℕ∞ω) ≤ ∞)) hx le_rfl).trans
      (hprofile q)
  have hbound := CompositionBounds.cNorm_le_sum
    (s := K) (r := r) (f := g ∘ f)
    (B := fun j ↦ compositionConstant A B j * T ^ (r - R))
    (fun j _ ↦ mul_nonneg (compositionConstant_nonneg hA hB j)
      (pow_nonneg (zero_le_one.trans hT) _)) (by
      intro j hj x hx
      exact (hjet j x hx).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hT (Nat.sub_le_sub_right hj R))
        (compositionConstant_nonneg hA hB j)))
  simpa only [Finset.sum_mul] using hbound

/-- The full seminorm profiles of two maps transfer through composition on
their original compact charts, with no loss of reserve. Coordinate and
external parameter variables may both be part of `X` and `E`
(`app:ch_regular_base:lem:buffered-interpolation`). -/
theorem hasDerivativeProfile_comp
    {K : Set X} {L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    {f : X → E} {g : E → F}
    (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x)
    (hg : ∀ y ∈ L, ContDiffAt ℝ ∞ g y) (hmap : MapsTo f K L)
    (A B : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    {T : ℝ} (hT : 1 ≤ T) {R : ℕ} (hR : 1 ≤ R)
    (hfProfile : HasDerivativeProfile K f R T B)
    (hgProfile : HasDerivativeProfile L g R T A) :
    HasDerivativeProfile K (g ∘ f) R T
      (fun r ↦ ∑ j ∈ Finset.range (r + 1), compositionConstant A B j) := by
  intro r
  have hjet (j : ℕ) (x : X) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ compositionConstant A B j * T ^ (j - R) := by
    apply norm_jet_comp_graded_le
      ((hf x hx).of_le (by simp : (j : ℕ∞ω) ≤ ∞))
      ((hg (f x) (hmap hx)).of_le (by simp : (j : ℕ∞ω) ≤ ∞)) le_rfl
      A B hA hB hT hR
    · intro q _
      exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
        (fun y hy ↦ (hg y hy).of_le (by simp : (q : ℕ∞ω) ≤ ∞))
          (hmap hx) le_rfl).trans (hgProfile q)
    · intro q _ _
      exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun y hy ↦ (hf y hy).of_le (by simp : (q : ℕ∞ω) ≤ ∞)) hx le_rfl).trans
        (hfProfile q)
  have hbound := CompositionBounds.cNorm_le_sum
    (s := K) (r := r) (f := g ∘ f)
    (B := fun j ↦ compositionConstant A B j * T ^ (r - R))
    (fun j _ ↦ mul_nonneg (compositionConstant_nonneg hA hB j)
      (pow_nonneg (zero_le_one.trans hT) _)) (by
      intro j hj x hx
      exact (hjet j x hx).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hT (Nat.sub_le_sub_right hj R))
        (compositionConstant_nonneg hA hB j)))
  simpa only [Finset.sum_mul] using hbound

end JanetCartan.DerivativeBounds
