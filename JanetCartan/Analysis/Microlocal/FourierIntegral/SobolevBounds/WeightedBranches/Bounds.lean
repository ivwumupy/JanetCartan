module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeightedBranches.Branches

/-!
# Uniform low-jet bounds for the nonlinear graph branches

Combining the proved derivative budget, uniform monomial counts and individual
primitive interpolation gives the exponent `(s-k)/s` in Step 3 of
`app:ch_regular_base:thm:actual-calculus`. No operator estimate is an input here.
The primitive majorants still need to be instantiated on the normalized boxes;
in particular the inverse primitive must be bounded using the mixed inverse gap.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local.Weighted
open Local FirstOutputJets
variable {n r : ℕ} {S : Euclidean n → Euclidean n → ℝ} {A F : FullAmplitude n r}

variable {U : Set (Point n)}

/-- Weights multiply with the exact total covector count. The primitive
majorants concern only the complete amplitude and actual mixed/inverse entries.
Source: `app:ch_regular_base:eq:joint-primitive-product`. -/
theorem weighted_term_norm_le_product (q : Option (ScalarIndex n) → ℕ → ℝ)
    (hq : ∀ a j, 0 ≤ q a j) (ρ : ℝ) (hρ : 0 ≤ ρ) (x y η : Euclidean n)
    (hA : ∀ w, ρ ^ frequencyOrder w * ‖jet w A x y η‖ ≤ q none w.length)
    (hS : ∀ a w, ρ ^ frequencyOrder w * ‖jet w (scalarPrimitive S a) x y η‖ ≤ q (some a) w.length)
    (t : Term n) : ρ ^ t.frequencyOrder * ‖t.value S A x y η‖ ≤ t.productBound q := by
  induction t with
  | amplitude w => simpa [Term.value, Term.frequencyOrder, Term.productBound, Term.orders] using hA w
  | factor a w t ih =>
    simp only [Term.value, multiply, Term.frequencyOrder, pow_add, norm_smul,
      Term.productBound, Term.orders, List.map_cons, List.prod_cons]
    calc
      _ = (ρ ^ frequencyOrder w * ‖jet w (scalarPrimitive S a) x y η‖) *
          (ρ ^ t.frequencyOrder * ‖t.value S A x y η‖) := by ring
      _ ≤ q (some a) w.length * t.productBound q :=
        mul_le_mul (hS a w) ih (by positivity) (hq _ _)

private theorem weighted_sum_values_le (ts : List (Term n)) (x y η : Euclidean n)
    (ρ B : ℝ) (hρ : 0 ≤ ρ) (f : ℕ)
    (hb : ∀ t ∈ ts, ρ ^ f * ‖t.value S A x y η‖ ≤ B) :
    ρ ^ f * ‖(ts.map (Term.value S A)).sum x y η‖ ≤ ts.length * B := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have ht := hb t (by simp)
    have hi := ih (fun u hu => hb u (by simp [hu]))
    have hh := mul_le_mul_of_nonneg_left
      (norm_add_le (t.value S A x y η) ((ts.map (Term.value S A)).sum x y η))
      (pow_nonneg hρ f)
    simp only [List.map_cons, List.sum_cons, Pi.add_apply, List.length_cons,
      Nat.cast_add, Nat.cast_one]
    nlinarith

/-- A bounded primitive expansion has a uniform interpolation constant.
Only individual primitive bounds enter the hypotheses. In particular the
number of monomials cannot secretly depend on the high majorant `H`.
Source: the high exponent calculation preceding `app:ch_regular_base:eq:fio-input`. -/
theorem WeightedExpansionOn.norm_le_interpolated
    (q : Option (ScalarIndex n) → ℕ → ℝ) (hq : ∀ a j, 0 ≤ q a j)
    (hmono : ∀ a, Monotone (q a)) (μ s d N m : ℕ) (hd : d ≤ s)
    (L K H : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : ∀ a, q a μ ≤ L) (hhigh : ∀ a, q a (μ + s) ≤ H)
    (hinterp : ∀ a j, μ < j → j < μ + s →
      q a j ≤ K * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
        q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (x y η : Euclidean n) (hpoint : ((x, y), η) ∈ U)
    (hA : ∀ w, ρ ^ frequencyOrder w * ‖FullAmplitudePrimitiveBudget.jet w A x y η‖ ≤ q none w.length)
    (hS : ∀ a w, ρ ^ frequencyOrder w * ‖FullAmplitudePrimitiveBudget.jet w (scalarPrimitive S a) x y η‖ ≤ q (some a) w.length)
    (f : ℕ) (hF : WeightedExpansionOn S A F U (d + μ) N m f) :
    ρ ^ f * ‖F x y η‖ ≤ (N * (K * L) ^ m) * H ^ ((d : ℝ) / s) := by
  obtain ⟨ts, he, hn, ht⟩ := hF
  have hb : ∀ t ∈ ts, ρ ^ f * ‖t.value S A x y η‖ ≤
      (K * L) ^ m * H ^ ((d : ℝ) / s) := by
    intro t hm
    rw [← (ht t hm).2.2]
    apply (weighted_term_norm_le_product q hq ρ hρ x y η hA hS t).trans
    apply (t.product_le_interpolated q hq hmono μ s d hd L K H hL hK hH
      hlow hhigh hinterp (ht t hm).1).trans
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hK hL) (ht t hm).2.1)
      (Real.rpow_nonneg (zero_le_one.trans hH) _)
  change ρ ^ f * ‖uncurry F ((x, y), η)‖ ≤ _
  rw [he hpoint]
  exact (weighted_sum_values_le ts x y η ρ _ hρ f hb).trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by positivity))

/-- Every low-seminorm jet of a concrete branch obeys the same high exponent.
The derivative and factor budgets are proved by the concrete branch theorems;
this lemma only performs their numerical interpolation.
Source: the low L² seminorm step before `app:ch_regular_base:eq:fio-input`. -/
theorem WeightedExpansionOn.jet_norm_le_interpolated
    (hU : IsOpen U) (h : SmoothPrimitivesOn S A U)
    (q : Option (ScalarIndex n) → ℕ → ℝ) (hq : ∀ a j, 0 ≤ q a j)
    (hmono : ∀ a, Monotone (q a)) (μ s k : ℕ)
    (L K H : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : ∀ a, q a μ ≤ L) (hhigh : ∀ a, q a (μ + s) ≤ H)
    (hinterp : ∀ a j, μ < j → j < μ + s →
      q a j ≤ K * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
        q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (x y η : Euclidean n) (hpoint : ((x, y), η) ∈ U)
    (hA : ∀ w, ρ ^ frequencyOrder w * ‖FullAmplitudePrimitiveBudget.jet w A x y η‖ ≤ q none w.length)
    (hS : ∀ a w, ρ ^ frequencyOrder w * ‖FullAmplitudePrimitiveBudget.jet w (scalarPrimitive S a) x y η‖ ≤ q (some a) w.length)
    (hF : WeightedExpansionOn S A F U (s - k) (branchTermCount n s) (s + 1) 0)
    (w : List (Coordinate n)) (hw : w.length ≤ μ) :
    ρ ^ frequencyOrder w * ‖FullAmplitudePrimitiveBudget.jet w F x y η‖ ≤ branchJetConstant n s μ L K * H ^ (((s - k : ℕ) : ℝ) / s) := by
  have he := (hF.jet hU h w).mono (Nat.add_le_add_left hw _)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hw)) le_rfl
  simpa only [Nat.zero_add, branchJetConstant] using he.norm_le_interpolated q hq hmono μ s (s - k) _ _ (Nat.sub_le _ _)
    L K H hL hK hH hlow hhigh hinterp ρ hρ x y η hpoint hA hS _

/-- Uniform bound for the actual forward branches, with both positions and
all covector derivatives in the low jet word. The high bound occurs with
exponent `(s-k)/s` only. Source: `app:ch_regular_base:eq:fio-input`, Step 3. -/
theorem graph_branch_jet_norm_le
    (hU : IsOpen U) (h : SmoothPrimitivesOn S A U)
    (q : Option (ScalarIndex n) → ℕ → ℝ) (hq : ∀ a j, 0 ≤ q a j)
    (hmono : ∀ a, Monotone (q a)) (μ s : ℕ) (is : List (Fin n)) (his : is.length ≤ s)
    (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S) (graphTransferDatum S) A is)
    (L K H : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : ∀ a, q a μ ≤ L) (hhigh : ∀ a, q a (μ + s) ≤ H)
    (hinterp : ∀ a j, μ < j → j < μ + s →
      q a j ≤ K * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
        q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (x y η : Euclidean n) (hpoint : ((x, y), η) ∈ U)
    (hA : ∀ w, ρ ^ frequencyOrder w * ‖FullAmplitudePrimitiveBudget.jet w A x y η‖ ≤ q none w.length)
    (hS : ∀ a w, ρ ^ frequencyOrder w * ‖FullAmplitudePrimitiveBudget.jet w (scalarPrimitive S a) x y η‖ ≤ q (some a) w.length)
    (w : List (Coordinate n)) (hw : w.length ≤ μ) :
    ρ ^ frequencyOrder w * ‖FullAmplitudePrimitiveBudget.jet w p.1 x y η‖ ≤ branchJetConstant n s μ L K *
      H ^ (((s - p.2.length : ℕ) : ℝ) / s) := by
  have he := (graph_branch_bounded_expansion hU h is p hp).mono
    (Nat.sub_le_sub_right his _) (branchTermCount_monotone n his) (Nat.add_le_add_right his 1)
  exact he.jet_norm_le_interpolated hU h q hq hmono
    μ s p.2.length L K H hL hK hH hlow hhigh hinterp ρ hρ x y η hpoint hA hS w hw

/-- Uniform bound for the literal reverse branches. `A` is already conjugate
transposed, and derivatives of the actual inverse are retained.
Source: `app:ch_regular_base:eq:actual-adjoint-trade` and `app:ch_regular_base:eq:fio-input`. -/
theorem adjoint_branch_jet_norm_le
    (hU : IsOpen U) (h : SmoothPrimitivesOn S A U)
    (q : Option (ScalarIndex n) → ℕ → ℝ) (hq : ∀ a j, 0 ≤ q a j)
    (hmono : ∀ a, Monotone (q a)) (μ s : ℕ) (is : List (Fin n)) (his : is.length ≤ s)
    (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S) (adjointTransferDatum S) A is)
    (L K H : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : ∀ a, q a μ ≤ L) (hhigh : ∀ a, q a (μ + s) ≤ H)
    (hinterp : ∀ a j, μ < j → j < μ + s →
      q a j ≤ K * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
        q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (x y η : Euclidean n) (hpoint : ((x, y), η) ∈ U)
    (hA : ∀ w, ρ ^ frequencyOrder w * ‖FullAmplitudePrimitiveBudget.jet w A x y η‖ ≤ q none w.length)
    (hS : ∀ a w, ρ ^ frequencyOrder w * ‖FullAmplitudePrimitiveBudget.jet w (scalarPrimitive S a) x y η‖ ≤ q (some a) w.length)
    (w : List (Coordinate n)) (hw : w.length ≤ μ) :
    ρ ^ frequencyOrder w * ‖FullAmplitudePrimitiveBudget.jet w p.1 x y η‖ ≤ branchJetConstant n s μ L K *
      H ^ (((s - p.2.length : ℕ) : ℝ) / s) := by
  have he := (adjoint_branch_bounded_expansion hU h is p hp).mono
    (Nat.sub_le_sub_right his _) (branchTermCount_monotone n his) (Nat.add_le_add_right his 1)
  exact he.jet_norm_le_interpolated hU h q hq hmono
    μ s p.2.length L K H hL hK hH hlow hhigh hinterp ρ hρ x y η hpoint hA hS w hw

end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local.Weighted
