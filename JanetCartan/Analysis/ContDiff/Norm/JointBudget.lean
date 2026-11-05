module

public import JanetCartan.Analysis.ContDiff.Norm.Defs
public import JanetCartan.Analysis.ContDiff.Norm.JointBudget.Algebra

import Mathlib.Tactic.Linarith

/-!
# Joint primitive derivative budgets and fixed-profile transfer

`cNorm_joint_primitive_product` proves the finite product estimate of
`app:ch_regular_base:eq:joint-primitive-product`, conditional on the precise
intermediate-order interpolation estimate. The constant is uniform over the
derivative orders, primitive assignments, and arrays with the given low bounds.
Repeated primitives and different target spaces are allowed. Only scalar norms are multiplied; this does
not reorder any underlying matrix factors.

`HasDerivativeProfile.transfer` and `cNorm_fixed_profile_family` prove
`app:cor:fixed-profile-transfer` from the stated finite-loss estimates, using
the actual truncated exponents. No interpolation theorem is needed for them.

As for `cNorm`, derivative suprema represent norms when the derivative images
are bounded. The pointwise corollary explicitly requires those bounds.
-/

@[expose] public noncomputable section

open scoped BigOperators ContDiff

namespace JanetCartan

namespace JointBudget

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The order-`j` derivative supremum used in
`app:ch_regular_base:eq:joint-primitive-product`. Use with bounded derivative images. -/
def derivativeSupNorm (s : Set E) (j : ℕ) (f : E → F) : ℝ :=
  sSup ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' s)

/-- Nonnegativity of the derivative supremum in
`app:ch_regular_base:eq:joint-primitive-product`. -/
theorem derivativeSupNorm_nonneg (s : Set E) (j : ℕ) (f : E → F) :
    0 ≤ derivativeSupNorm s j f := by
  apply Real.sSup_nonneg
  rintro _ ⟨x, _, rfl⟩
  exact norm_nonneg _

/-- Nonnegativity of the seminorm in
`app:ch_regular_base:eq:joint-primitive-product`. -/
theorem cNorm_nonneg (s : Set E) (r : ℕ) (f : E → F) : 0 ≤ cNorm s r f :=
  Finset.sum_nonneg fun j _ ↦ derivativeSupNorm_nonneg s j f

/-- Monotonicity in derivative order, for the endpoint cases of
`app:ch_regular_base:eq:joint-primitive-product`. -/
theorem cNorm_monotone (s : Set E) (f : E → F) : Monotone (fun r ↦ cNorm s r f) := by
  intro r k hrk
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hrk 1))
    (fun j _ _ ↦ derivativeSupNorm_nonneg s j f)

/-- A derivative supremum is bounded by the full seminorm at the same order
(`app:ch_regular_base:eq:joint-primitive-product`). -/
theorem derivativeSupNorm_le_cNorm (s : Set E) (j : ℕ) (f : E → F) :
    derivativeSupNorm s j f ≤ cNorm s j f :=
  Finset.single_le_sum (fun q _ ↦ derivativeSupNorm_nonneg s q f)
    (Finset.mem_range.mpr (Nat.lt_succ_self j))

/-- Bounded derivative images make the supremum control pointwise derivatives
in `app:ch_regular_base:eq:joint-primitive-product`. -/
theorem norm_iteratedFDeriv_le_derivativeSupNorm
    (s : Set E) (j : ℕ) (f : E → F)
    (hbounded : BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' s))
    {x : E} (hx : x ∈ s) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ derivativeSupNorm s j f :=
  le_csSup hbounded ⟨x, hx, rfl⟩

end JointBudget

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `app:ch_regular_base:eq:joint-primitive-product`, in the stronger form
with full `C^j` seminorms on the left. Interpolation at strict intermediate
orders is the sole analytic input. `K ≥ 1` bounds its finitely many constants;
`B ≥ 1` bounds the baseline norms. This includes `W = 0` and empty products. -/
theorem cNorm_joint_primitive_product
    {ι α : Type*} {V : ι → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    (I : Finset ι) (factors : Finset α) (s : Set E)
    (f : ∀ i, E → V i) (b : ι → ℕ) (index : α → ι) (j : α → ℕ)
    (W : ℕ) (B K : ℝ) (hB : 1 ≤ B) (hK : 1 ≤ K)
    (hlow : ∀ i ∈ I, cNorm s (b i) (f i) ≤ B)
    (hindex : ∀ h ∈ factors, index h ∈ I)
    (hbudget : ∑ h ∈ factors, (j h - b (index h)) ≤ W)
    (hinterp : ∀ i ∈ I, ∀ q, b i < q → q < b i + W →
      cNorm s q (f i) ≤
        K * cNorm s (b i) (f i) ^ (1 - ((q - b i : ℕ) : ℝ) / W) *
          cNorm s (b i + W) (f i) ^ (((q - b i : ℕ) : ℝ) / W)) :
    ∏ h ∈ factors, cNorm s (j h) (f (index h)) ≤
      (K * B) ^ factors.card * (1 + ∑ i ∈ I, cNorm s (b i + W) (f i)) :=
  JointBudget.finite_product_le_one_high I factors (fun i q ↦ cNorm s q (f i))
    b index j W B K (fun i _ q ↦ JointBudget.cNorm_nonneg s q (f i))
    (fun i _ ↦ JointBudget.cNorm_monotone s (f i)) hB hK hlow hindex hbudget hinterp

/-- The derivative-supremum version of
`app:ch_regular_base:eq:joint-primitive-product`, conditional on interpolation.
Repeated primitive occurrences share one high norm on the right. -/
theorem derivativeSupNorm_joint_primitive_product
    {ι α : Type*} {V : ι → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    (I : Finset ι) (factors : Finset α) (s : Set E)
    (f : ∀ i, E → V i) (b : ι → ℕ) (index : α → ι) (j : α → ℕ)
    (W : ℕ) (B K : ℝ) (hB : 1 ≤ B) (hK : 1 ≤ K)
    (hlow : ∀ i ∈ I, cNorm s (b i) (f i) ≤ B)
    (hindex : ∀ h ∈ factors, index h ∈ I)
    (hbudget : ∑ h ∈ factors, (j h - b (index h)) ≤ W)
    (hinterp : ∀ i ∈ I, ∀ q, b i < q → q < b i + W →
      cNorm s q (f i) ≤
        K * cNorm s (b i) (f i) ^ (1 - ((q - b i : ℕ) : ℝ) / W) *
          cNorm s (b i + W) (f i) ^ (((q - b i : ℕ) : ℝ) / W)) :
    ∏ h ∈ factors, JointBudget.derivativeSupNorm s (j h) (f (index h)) ≤
      (K * B) ^ factors.card * (1 + ∑ i ∈ I, cNorm s (b i + W) (f i)) := by
  apply le_trans (Finset.prod_le_prod₀
    (fun h _ ↦ JointBudget.derivativeSupNorm_nonneg s (j h) (f (index h)))
    (fun h _ ↦ JointBudget.derivativeSupNorm_le_cNorm s (j h) (f (index h))))
  exact cNorm_joint_primitive_product I factors s f b index j W B K
    hB hK hlow hindex hbudget hinterp

/-- `app:ch_regular_base:eq:joint-primitive-product` with its uniform constant
quantified before the primitive arrays and derivative assignments. The explicit
analytic premise is the usual interpolation theorem, with a separate constant
for each baseline and intermediate order. No unfinished interpolation proof is used. -/
theorem exists_joint_primitive_product_constant
    {ι α : Type*} {V : ι → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    (I : Finset ι) (factors : Finset α) (s : Set E)
    (b : ι → ℕ) (W : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hinterp : ∀ i ∈ I, ∀ q, b i < q → q < b i + W →
      ∃ L : ℝ, 0 < L ∧ ∀ u : E → V i, ContDiff ℝ ∞ u →
        cNorm s q u ≤
          L * cNorm s (b i) u ^ (1 - ((q - b i : ℕ) : ℝ) / W) *
            cNorm s (b i + W) u ^ (((q - b i : ℕ) : ℝ) / W)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ∀ i, E → V i,
      (∀ i ∈ I, ContDiff ℝ ∞ (f i)) →
      (∀ i ∈ I, cNorm s (b i) (f i) ≤ B) →
      ∀ (index : α → ι) (j : α → ℕ),
        (∀ h ∈ factors, index h ∈ I) →
        (∑ h ∈ factors, (j h - b (index h)) ≤ W) →
        ∏ h ∈ factors, JointBudget.derivativeSupNorm s (j h) (f (index h)) ≤
          C * (1 + ∑ i ∈ I, cNorm s (b i + W) (f i)) := by
  classical
  have hchoice : ∀ i q, ∃ L : ℝ, 0 < L ∧
      (i ∈ I → b i < q → q < b i + W → ∀ u : E → V i, ContDiff ℝ ∞ u →
        cNorm s q u ≤
          L * cNorm s (b i) u ^ (1 - ((q - b i : ℕ) : ℝ) / W) *
            cNorm s (b i + W) u ^ (((q - b i : ℕ) : ℝ) / W)) := by
    intro i q
    by_cases h : i ∈ I ∧ b i < q ∧ q < b i + W
    · obtain ⟨L, hL, hLu⟩ := hinterp i h.1 q h.2.1 h.2.2
      exact ⟨L, hL, fun _ _ _ ↦ hLu⟩
    · exact ⟨1, zero_lt_one, fun hi hbq hqb ↦ False.elim (h ⟨hi, hbq, hqb⟩)⟩
  choose L hL hLu using hchoice
  let K := 1 + ∑ i ∈ I, ∑ q ∈ Finset.range (b i + W), |L i q|
  have hsums (i : ι) : 0 ≤ ∑ q ∈ Finset.range (b i + W), |L i q| :=
    Finset.sum_nonneg fun q _ ↦ abs_nonneg (L i q)
  have hK : 1 ≤ K := by
    dsimp [K]
    linarith [Finset.sum_nonneg (fun i (_ : i ∈ I) ↦ hsums i)]
  have hLK (i : ι) (hi : i ∈ I) (q : ℕ) (hq : q < b i + W) : L i q ≤ K := by
    have hqsum := Finset.single_le_sum
      (fun q (_ : q ∈ Finset.range (b i + W)) ↦ abs_nonneg (L i q))
      (Finset.mem_range.mpr hq)
    have hisum := Finset.single_le_sum (fun i (_ : i ∈ I) ↦ hsums i) hi
    have habs := le_abs_self (L i q)
    dsimp [K]
    linarith
  refine ⟨(K * B) ^ factors.card, pow_pos (mul_pos (by linarith) (by linarith)) _, ?_⟩
  intro f hf hlow index j hindex hbudget
  apply derivativeSupNorm_joint_primitive_product I factors s f b index j W B K
    hB hK hlow hindex hbudget
  intro i hi q hbq hqb
  apply (hLu i q hi hbq hqb (f i) (hf i hi)).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hLK i hi q hqb)
      (Real.rpow_nonneg (JointBudget.cNorm_nonneg s (b i) (f i)) _))
    (Real.rpow_nonneg (JointBudget.cNorm_nonneg s (b i + W) (f i)) _)

/-- `app:cor:fixed-profile-transfer`: transfer through a fixed construction
with loss `c`, retaining the actual truncated exponent `r - ν`. The premise
is the source's finite-loss estimate; no claim about proving that estimate is made. -/
theorem HasDerivativeProfile.transfer
    {s : Set E} {f : E → F} {g : E → G} {R ν c : ℕ} {T : ℝ}
    {A C : ℕ → ℝ} (hf : HasDerivativeProfile s f R T A)
    (hT : 1 ≤ T) (hA : ∀ r, 0 ≤ A r) (hC : ∀ r, 0 ≤ C r)
    (hloss : c + ν ≤ R)
    (hconstruction : ∀ r, cNorm s r g ≤ C r * (1 + cNorm s (r + c) f)) :
    HasDerivativeProfile s g ν T (fun r ↦ C r * (1 + A (r + c))) := by
  intro r
  exact JointBudget.fixed_profile_transfer_bound hT (hA (r + c)) (hC r) hloss
    (hf (r + c)) (hconstruction r)

/-- `app:cor:fixed-profile-transfer` for a fixed finite family. Summing the
individual constants gives one constant for every array in the family. -/
theorem cNorm_fixed_profile_family
    {ι : Type*} {V : ι → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    (I : Finset ι) {s : Set E} {f : E → F} (g : ∀ i, E → V i)
    {R ν cMax : ℕ} {T : ℝ} {A : ℕ → ℝ} (c : ι → ℕ) (C : ι → ℕ → ℝ)
    (hf : HasDerivativeProfile s f R T A)
    (hT : 1 ≤ T) (hA : ∀ r, 0 ≤ A r) (hC : ∀ i ∈ I, ∀ r, 0 ≤ C i r)
    (hshift : ∀ i ∈ I, c i ≤ cMax) (hloss : cMax + ν ≤ R)
    (hconstruction : ∀ i ∈ I, ∀ r,
      cNorm s r (g i) ≤ C i r * (1 + cNorm s (r + c i) f)) :
    ∀ i ∈ I, HasDerivativeProfile s (g i) ν T
      (fun r ↦ ∑ k ∈ I, C k r * (1 + A (r + c k))) := by
  intro i hi r
  have hiLoss : c i + ν ≤ R := (Nat.add_le_add_right (hshift i hi) ν).trans hloss
  have hbound := hf.transfer hT hA (hC i hi) hiLoss (hconstruction i hi) r
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (le_trans zero_le_one hT) _)
  exact Finset.single_le_sum
    (fun k hk ↦ mul_nonneg (hC k hk r) (add_nonneg zero_le_one (hA (r + c k)))) hi

end JanetCartan
