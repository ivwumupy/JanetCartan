module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveBudget.Estimates

/-!
# Joint primitive budgets for forward and literal-adjoint graph branches

The concrete amplitude part of Step 3 of `app:ch_regular_base:thm:actual-calculus`.
The branch expansions and the shared derivative/excess budgets are proved from
primitive smoothness. All masks remain in the complete matrix amplitude, and
the scalar primitives are the actual mixed matrix and its actual inverse.

`graph_branch_primitive_budget` and `adjoint_branch_primitive_budget` supply the
finite expansions consumed by the parent strong Sobolev estimate
`app:ch_regular_base:eq:fio-input`. `Term.product_le_interpolated` and
`Term.norm_value_le_interpolated` provide the product estimate with exponent
`(s-k)/s` from individual low/high primitive interpolation inputs. The parent
must instantiate these inputs on normalized boxes and use the low L² bound;
no high operator bound or operator derivative identity is assumed here.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget
variable {n r : ℕ} {S : Euclidean n → Euclidean n → ℝ} {A : FullAmplitude n r}

/-- Joint total and excess budgets for the actual forward branch, including
all physical and covector derivatives in the low seminorm word. Source:
Step 3 of `app:ch_regular_base:thm:actual-calculus`, after
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graph_branch_primitive_budget (h : SmoothPrimitives S A)
    (is : List (Fin n)) (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
      (graphTransferDatum S) A is)
    (w : List (Coordinate n)) (μ : ℕ) (hw : w.length ≤ μ) :
    ∃ ts : List (Term n), jet w p.1 = (ts.map (Term.value S A)).sum ∧
      ∀ t ∈ ts, t.order ≤ is.length - p.2.length + μ ∧
        OrderedProducts.excessOrder (fun _ => μ) t.orders ≤ is.length - p.2.length :=
  (graph_branch_expansion h is p hp).jet_budget h w μ hw

/-- Joint total and excess budgets for the actual reverse branch. The input
`A` is already conjugate-transposed; derivatives of the actual inverse are
included among the scalar factors. Source: Step 3 of
`app:ch_regular_base:thm:actual-calculus` and
`app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem adjoint_branch_primitive_budget (h : SmoothPrimitives S A)
    (is : List (Fin n)) (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
      (adjointTransferDatum S) A is)
    (w : List (Coordinate n)) (μ : ℕ) (hw : w.length ≤ μ) :
    ∃ ts : List (Term n), jet w p.1 = (ts.map (Term.value S A)).sum ∧
      ∀ t ∈ ts, t.order ≤ is.length - p.2.length + μ ∧
        OrderedProducts.excessOrder (fun _ => μ) t.orders ≤ is.length - p.2.length :=
  (adjoint_branch_expansion h is p hp).jet_budget h w μ hw

/-- Pointwise product bound ready for the normalized symbol seminorms: set
`d = s-k` for any term in either concrete branch budget. Only individual
primitive jets and their interpolation are inputs. Source: the total high
exponent calculation in Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Term.norm_value_le_interpolated
    (q : Option (ScalarIndex n) → ℕ → ℝ) (hq : ∀ a j, 0 ≤ q a j)
    (hmono : ∀ a, Monotone (q a)) (μ s d : ℕ) (hd : d ≤ s)
    (L K H : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : ∀ a, q a μ ≤ L) (hhigh : ∀ a, q a (μ + s) ≤ H)
    (hinterp : ∀ a j, μ < j → j < μ + s →
      q a j ≤ K * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
        q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s))
    (x y η : Euclidean n)
    (hA : ∀ w, ‖jet w A x y η‖ ≤ q none w.length)
    (hS : ∀ a w, ‖jet w (scalarPrimitive S a) x y η‖ ≤ q (some a) w.length)
    (t : Term n) (ht : t.order ≤ d + μ) :
    ‖t.value S A x y η‖ ≤ (K * L) ^ t.orders.length * H ^ ((d : ℝ) / s) :=
  (t.norm_value_le_product q hq x y η hA hS).trans
    (t.product_le_interpolated q hq hmono μ s d hd L K H hL hK hH hlow hhigh hinterp ht)

end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget
