module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveBudget.Branches

/-!
# Joint excess and product estimates for the concrete branch expansion

The fixed-baseline count in Step 3 of `app:ch_regular_base:thm:actual-calculus`.
Actual individual primitive jet estimates and their scalar interpolation bounds
remain explicit inputs. No operator estimate is used here.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget
variable {n r : ℕ} {S : Euclidean n → Euclidean n → ℝ} {A F : FullAmplitude n r}

/-- Subtracting the same low baseline from every factor costs at least one
baseline from the total order. Source: Step 3, following
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem Term.excess_le (t : Term n) (μ : ℕ) :
    OrderedProducts.excessOrder (fun _ => μ) t.orders ≤ t.order - μ := by
  induction t with
  | amplitude w => simp [orders, order, OrderedProducts.excessOrder]
  | factor a w t ih =>
    simp only [orders, OrderedProducts.excessOrder, List.map_cons, List.sum_cons] at *
    simp only [order]
    omega

/-- The low seminorm reserve is spent only once in the complete monomial:
`∑ (r_h-μ)₊ ≤ d` if `∑ r_h ≤ d+μ`. Source: Step 3 of
`app:ch_regular_base:thm:actual-calculus`. -/
theorem Term.excess_le_of_order_le (t : Term n) (μ d : ℕ) (ht : t.order ≤ d + μ) :
    OrderedProducts.excessOrder (fun _ => μ) t.orders ≤ d :=
  (t.excess_le μ).trans (by omega)

/-- The primitive jet word has a single total/excess budget, simultaneously
for all factors. Source: the low operator seminorm count in Step 3.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Expansion.jet_budget (h : SmoothPrimitives S A) {d : ℕ}
    (hF : Expansion S A F d) (w : List (Coordinate n)) (μ : ℕ) (hw : w.length ≤ μ) :
    ∃ ts : List (Term n), FullAmplitudePrimitiveBudget.jet w F = (ts.map (Term.value S A)).sum ∧
      ∀ t ∈ ts, t.order ≤ d + μ ∧
        OrderedProducts.excessOrder (fun _ => μ) t.orders ≤ d := by
  obtain ⟨ts, he, ht⟩ := hF.jet h w
  refine ⟨ts, he, fun t hm => ?_⟩
  have hb : t.order ≤ d + μ := (ht t hm).trans (Nat.add_le_add_left hw d)
  exact ⟨hb, t.excess_le_of_order_le μ d hb⟩

/-- A scalar majorant of a complete monomial, with repeated entries retained.
Source: `app:ch_regular_base:eq:joint-primitive-product`. -/
def Term.productBound (q : Option (ScalarIndex n) → ℕ → ℝ) (t : Term n) : ℝ :=
  (t.orders.map fun p => q p.1 p.2).prod

/-- The complete matrix product is controlled by the product of its scalar
jet majorants. Source: `app:ch_regular_base:eq:joint-primitive-product`. -/
theorem Term.norm_value_le_product (q : Option (ScalarIndex n) → ℕ → ℝ)
    (hq : ∀ a j, 0 ≤ q a j) (x y η : Euclidean n)
    (hA : ∀ w, ‖jet w A x y η‖ ≤ q none w.length)
    (hS : ∀ a w, ‖jet w (scalarPrimitive S a) x y η‖ ≤ q (some a) w.length)
    (t : Term n) : ‖t.value S A x y η‖ ≤ t.productBound q := by
  induction t with
  | amplitude w => simpa [value, productBound, orders] using hA w
  | factor a w t ih =>
    simp only [value, multiply, productBound, orders, List.map_cons, List.prod_cons]
    exact (norm_smul_le _ _).trans (mul_le_mul (hS a w) ih (norm_nonneg _) (hq _ _))

private theorem list_product_rpow
    (q : Option (ScalarIndex n) → ℕ → ℝ) (hq : ∀ a j, 0 ≤ q a j)
    (l : OrderedProducts.Monomial (Option (ScalarIndex n))) (μ s : ℕ) (C H : ℝ)
    (hC : 0 ≤ C) (hH : 1 ≤ H)
    (hf : ∀ p ∈ l, q p.1 p.2 ≤ C * H ^ (((p.2 - μ : ℕ) : ℝ) / s)) :
    (l.map fun p => q p.1 p.2).prod ≤
      C ^ l.length * H ^ ((OrderedProducts.excessOrder (fun _ => μ) l : ℝ) / s) := by
  induction l with
  | nil => simp [OrderedProducts.excessOrder]
  | cons p l ih =>
    have hp := hf p (by simp)
    have hl := ih (fun p hp => hf p (by simp [hp]))
    calc
      ((p :: l).map fun p => q p.1 p.2).prod ≤
          (C * H ^ (((p.2 - μ : ℕ) : ℝ) / s)) *
            (C ^ l.length * H ^ ((OrderedProducts.excessOrder (fun _ => μ) l : ℝ) / s)) := by
        simp only [List.map_cons, List.prod_cons]
        exact mul_le_mul hp hl (List.prod_nonneg (by
          intro v hv
          obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
          exact hq _ _)) (by positivity)
      _ = C ^ (p :: l).length *
          H ^ ((OrderedProducts.excessOrder (fun _ => μ) (p :: l) : ℝ) / s) := by
        simp only [List.length_cons, pow_succ, OrderedProducts.excessOrder,
          List.map_cons, List.sum_cons, Nat.cast_add, add_div]
        rw [Real.rpow_add (by linarith : 0 < H)]
        ring

/-- Interpolation of the complete product keeps the exponent `d/s`.
The inputs concern only individual primitive majorants: low bounds, a common
high bound at `μ+s`, and intermediate interpolation. Source: the exponent
`(s-k)/s` argument in Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Term.product_le_interpolated
    (q : Option (ScalarIndex n) → ℕ → ℝ) (hq : ∀ a j, 0 ≤ q a j)
    (hmono : ∀ a, Monotone (q a)) (μ s d : ℕ) (hd : d ≤ s)
    (L K H : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : ∀ a, q a μ ≤ L) (hhigh : ∀ a, q a (μ + s) ≤ H)
    (hinterp : ∀ a j, μ < j → j < μ + s →
      q a j ≤ K * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
        q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s))
    (t : Term n) (ht : t.order ≤ d + μ) :
    t.productBound q ≤ (K * L) ^ t.orders.length * H ^ ((d : ℝ) / s) := by
  have hf : ∀ p ∈ t.orders, q p.1 p.2 ≤
      (K * L) * H ^ (((p.2 - μ : ℕ) : ℝ) / s) := by
    intro p hp
    have hporder : p.2 ≤ t.order := by
      rw [← t.totalOrder_orders]
      exact List.le_sum_of_mem (List.mem_map.mpr ⟨p, hp, rfl⟩)
    exact JointBudget.interpolation_le_scaled_rpow (q p.1) μ s p.2 L K H
      (hq p.1) (hmono p.1) hL hK hH (hlow p.1) (hhigh p.1) (by omega) (hinterp p.1 p.2)
  apply (list_product_rpow q hq t.orders μ s (K * L) H (by positivity) hH hf).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hH
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg s)
  exact_mod_cast t.excess_le_of_order_le μ d ht

end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget
