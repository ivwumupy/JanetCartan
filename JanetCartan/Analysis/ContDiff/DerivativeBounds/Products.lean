module

public import JanetCartan.Analysis.ContDiff.DerivativeBounds.RealAlgebra
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Analysis.ContDiff.Norm.JointBudget

/-!
# Finite products of derivative norms

The factors may have different target spaces and are evaluated on the
original fixed chart. Only their scalar norms are multiplied, so the result
does not commute any underlying matrix factors. Both the native natural
reserve and the literal real positive-part versions are retained.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff BigOperators

namespace JanetCartan.DerivativeBounds

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual derivative-supremum product in
`app:ch_regular_base:eq:joint-primitive-product`, together with its pointwise
consequence. There is one reserve for the total order; repeated primitive
fields are allowed among the factors. -/
theorem finite_product_derivative_bounds
    {ι : Type*} {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (I : Finset ι) {K : Set X} (hK : IsCompact K) (f : ∀ i, X → E i)
    (hf : ∀ i ∈ I, ∀ x ∈ K, ContDiffAt ℝ ∞ (f i) x)
    (C : ι → ℕ → ℝ) (hC : ∀ i ∈ I, ∀ r, 0 ≤ C i r)
    {T : ℝ} (hT : 1 ≤ T) (R : ℕ)
    (hprofile : ∀ i ∈ I, HasDerivativeProfile K (f i) R T (C i)) (j : ι → ℕ) :
    (∏ i ∈ I, JointBudget.derivativeSupNorm K (j i) (f i)) ≤
      (∏ i ∈ I, C i (j i)) * T ^ ((∑ i ∈ I, j i) - R) ∧
      ∀ x : ι → X, (∀ i ∈ I, x i ∈ K) →
        (∏ i ∈ I, ‖iteratedFDeriv ℝ (j i) (f i) (x i)‖) ≤
          (∏ i ∈ I, C i (j i)) * T ^ ((∑ i ∈ I, j i) - R) := by
  constructor
  · exact finite_product_reserve_bound I j
      (fun i ↦ JointBudget.derivativeSupNorm K (j i) (f i)) (fun i ↦ C i (j i)) hT R
      (fun i _ ↦ JointBudget.derivativeSupNorm_nonneg _ _ _)
      (fun i hi ↦ hC i hi _) (fun i hi ↦
        (JointBudget.derivativeSupNorm_le_cNorm _ _ _).trans (hprofile i hi (j i)))
  · intro x hx
    apply finite_product_reserve_bound I j
      (fun i ↦ ‖iteratedFDeriv ℝ (j i) (f i) (x i)‖) (fun i ↦ C i (j i)) hT R
      (fun _ _ ↦ norm_nonneg _) (fun i hi ↦ hC i hi _)
    intro i hi
    exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hf i hi y hy).of_le (by simp : ((j i : ℕ) : ℕ∞ω) ≤ ∞))
        (hx i hi) le_rfl).trans (hprofile i hi (j i))

/-- The same derivative product for an arbitrary nonnegative REAL reserve.
This is the literal positive-part formulation of
`app:lem:elementary-interpolation-jets`; no rounding of the reserve occurs. -/
theorem finite_product_derivative_bounds_real_reserve
    {ι : Type*} {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (I : Finset ι) {K : Set X} (hK : IsCompact K) (f : ∀ i, X → E i)
    (hf : ∀ i ∈ I, ∀ x ∈ K, ContDiffAt ℝ ∞ (f i) x)
    (C : ι → ℕ → ℝ) (hC : ∀ i ∈ I, ∀ r, 0 ≤ C i r)
    {T R : ℝ} (hT : 1 ≤ T) (hR : 0 ≤ R)
    (hprofile : ∀ i ∈ I, ∀ r : ℕ, cNorm K r (f i) ≤ C i r * T ^ (max ((r : ℝ) - R) 0))
    (j : ι → ℕ) :
    (∏ i ∈ I, JointBudget.derivativeSupNorm K (j i) (f i)) ≤
      (∏ i ∈ I, C i (j i)) * T ^ (max (((∑ i ∈ I, j i : ℕ) : ℝ) - R) 0) ∧
      ∀ x : ι → X, (∀ i ∈ I, x i ∈ K) →
        (∏ i ∈ I, ‖iteratedFDeriv ℝ (j i) (f i) (x i)‖) ≤
          (∏ i ∈ I, C i (j i)) * T ^ (max (((∑ i ∈ I, j i : ℕ) : ℝ) - R) 0) := by
  constructor
  · have h := finite_product_real_reserve_bound I (fun i ↦ (j i : ℝ))
      (fun i ↦ JointBudget.derivativeSupNorm K (j i) (f i)) (fun i ↦ C i (j i)) hT hR
      (fun _ _ ↦ Nat.cast_nonneg _) (fun i _ ↦ JointBudget.derivativeSupNorm_nonneg _ _ _)
      (fun i hi ↦ hC i hi _) (fun i hi ↦
        (JointBudget.derivativeSupNorm_le_cNorm _ _ _).trans (hprofile i hi (j i)))
    simpa only [← Nat.cast_sum] using h
  · intro x hx
    have h := finite_product_real_reserve_bound I (fun i ↦ (j i : ℝ))
      (fun i ↦ ‖iteratedFDeriv ℝ (j i) (f i) (x i)‖) (fun i ↦ C i (j i)) hT hR
      (fun _ _ ↦ Nat.cast_nonneg _) (fun _ _ ↦ norm_nonneg _) (fun i hi ↦ hC i hi _)
      (fun i hi ↦ (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun y hy ↦ (hf i hi y hy).of_le (by simp : ((j i : ℕ) : ℕ∞ω) ≤ ∞))
          (hx i hi) le_rfl).trans (hprofile i hi (j i)))
    simpa only [← Nat.cast_sum] using h

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pairing two original arrays preserves their reserve. This provides the
product-domain input for the smooth coefficient and flow-suspension clauses
of `app:lem:elementary-interpolation-jets` and
`app:ch_regular_base:lem:buffered-interpolation`. -/
theorem hasDerivativeProfile_prodMk {K : Set X} (hK : IsCompact K)
    {f : X → E} {g : X → F}
    (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x) (hg : ∀ x ∈ K, ContDiffAt ℝ ∞ g x)
    (A B : ℕ → ℝ) (hA : ∀ r, 0 ≤ A r) (hB : ∀ r, 0 ≤ B r)
    {T : ℝ} (hT : 1 ≤ T) (R : ℕ)
    (hfProfile : HasDerivativeProfile K f R T A)
    (hgProfile : HasDerivativeProfile K g R T B) :
    HasDerivativeProfile K (fun x ↦ (f x, g x)) R T
      (fun r ↦ (r + 1 : ℝ) * (A r + B r)) := by
  intro r
  let D := (A r + B r) * T ^ (r - R)
  have hD : 0 ≤ D := mul_nonneg (add_nonneg (hA r) (hB r))
    (pow_nonneg (zero_le_one.trans hT) _)
  have hb := CompositionBounds.cNorm_le_sum (s := K) (r := r)
    (f := fun x ↦ (f x, g x)) (B := fun _ ↦ D) (fun _ _ ↦ hD) (by
      intro j hj x hx
      rw [iteratedFDeriv_prodMk (hf x hx) (hg x hx) (by simp : (j : ℕ∞ω) ≤ ∞),
        ContinuousMultilinearMap.opNorm_prod]
      have hfj := (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun y hy ↦ (hf y hy).of_le (by simp : (r : ℕ∞ω) ≤ ∞)) hx hj).trans (hfProfile r)
      have hgj := (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun y hy ↦ (hg y hy).of_le (by simp : (r : ℕ∞ω) ≤ ∞)) hx hj).trans (hgProfile r)
      apply max_le
      · exact hfj.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hB r))
          (pow_nonneg (zero_le_one.trans hT) (r - R)))
      · exact hgj.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hA r))
          (pow_nonneg (zero_le_one.trans hT) (r - R))))
  simpa only [D, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mul_assoc] using hb

/-- A fixed linear coordinate map on the output preserves the reserve.
This includes fixed parameter projections and coordinate relabelings in
`app:cor:fixed-profile-transfer` and the flow suspension. -/
theorem hasDerivativeProfile_postCLM {K : Set X} (hK : IsCompact K)
    {f : X → E} (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x) (L : E →L[ℝ] F)
    (A : ℕ → ℝ) (hA : ∀ r, 0 ≤ A r) {T : ℝ} (hT : 1 ≤ T) (R : ℕ)
    (hprofile : HasDerivativeProfile K f R T A) :
    HasDerivativeProfile K (L ∘ f) R T
      (fun r ↦ (r + 1 : ℝ) * ‖L‖ * A r) := by
  intro r
  let D := ‖L‖ * A r * T ^ (r - R)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (norm_nonneg _) (hA r))
    (pow_nonneg (zero_le_one.trans hT) _)
  have hb := CompositionBounds.cNorm_le_sum (s := K) (r := r) (f := L ∘ f)
    (B := fun _ ↦ D) (fun _ _ ↦ hD) (by
      intro j hj x hx
      have hsrc := (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun y hy ↦ (hf y hy).of_le (by simp : (r : ℕ∞ω) ≤ ∞)) hx hj).trans (hprofile r)
      have hh := (L.norm_iteratedFDeriv_comp_left (hf x hx)
        (by simp : (j : ℕ∞ω) ≤ ∞)).trans
          (mul_le_mul_of_nonneg_left hsrc (norm_nonneg _))
      simpa only [D, mul_assoc] using hh)
  simpa only [D, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mul_assoc] using hb

end JanetCartan.DerivativeBounds
