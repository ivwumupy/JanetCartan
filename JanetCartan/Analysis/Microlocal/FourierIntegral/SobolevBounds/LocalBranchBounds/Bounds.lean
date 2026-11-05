module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.LocalBranchBounds.Branches

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
namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local
variable {n r : ℕ} {S : Euclidean n → Euclidean n → ℝ} {A F : FullAmplitude n r}

variable {U : Set (Point n)}

/-- A bounded primitive expansion has a uniform interpolation constant.
Only individual primitive bounds enter the hypotheses. In particular the
number of monomials cannot secretly depend on the high majorant `H`.
Source: the high exponent calculation preceding `app:ch_regular_base:eq:fio-input`. -/
theorem BoundedExpansionOn.norm_le_interpolated
    (q : Option (ScalarIndex n) → ℕ → ℝ) (hq : ∀ a j, 0 ≤ q a j)
    (hmono : ∀ a, Monotone (q a)) (μ s d N m : ℕ) (hd : d ≤ s)
    (L K H : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : ∀ a, q a μ ≤ L) (hhigh : ∀ a, q a (μ + s) ≤ H)
    (hinterp : ∀ a j, μ < j → j < μ + s →
      q a j ≤ K * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
        q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s))
    (x y η : Euclidean n) (hpoint : ((x, y), η) ∈ U)
    (hA : ∀ w, ‖FullAmplitudePrimitiveBudget.jet w A x y η‖ ≤ q none w.length)
    (hS : ∀ a w, ‖FullAmplitudePrimitiveBudget.jet w (scalarPrimitive S a) x y η‖ ≤ q (some a) w.length)
    (hF : BoundedExpansionOn S A F U (d + μ) N m) :
    ‖F x y η‖ ≤ (N * (K * L) ^ m) * H ^ ((d : ℝ) / s) := by
  obtain ⟨ts, he, hn, ht⟩ := hF
  have hb : FullAmplitudePrimitiveBudget.BoundedExpansion S A
      (ts.map (Term.value S A)).sum (d + μ) N m := ⟨ts, rfl, hn, ht⟩
  change ‖uncurry F ((x, y), η)‖ ≤ _
  rw [he hpoint]
  exact hb.norm_le_interpolated q hq hmono μ s d N m hd L K H hL hK hH
    hlow hhigh hinterp x y η hA hS

/-- Every low-seminorm jet of a concrete branch obeys the same high exponent.
The derivative and factor budgets are proved by the concrete branch theorems;
this lemma only performs their numerical interpolation.
Source: the low L² seminorm step before `app:ch_regular_base:eq:fio-input`. -/
theorem BoundedExpansionOn.jet_norm_le_interpolated
    (hU : IsOpen U) (h : SmoothPrimitivesOn S A U)
    (q : Option (ScalarIndex n) → ℕ → ℝ) (hq : ∀ a j, 0 ≤ q a j)
    (hmono : ∀ a, Monotone (q a)) (μ s k : ℕ)
    (L K H : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : ∀ a, q a μ ≤ L) (hhigh : ∀ a, q a (μ + s) ≤ H)
    (hinterp : ∀ a j, μ < j → j < μ + s →
      q a j ≤ K * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
        q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s))
    (x y η : Euclidean n) (hpoint : ((x, y), η) ∈ U)
    (hA : ∀ w, ‖FullAmplitudePrimitiveBudget.jet w A x y η‖ ≤ q none w.length)
    (hS : ∀ a w, ‖FullAmplitudePrimitiveBudget.jet w (scalarPrimitive S a) x y η‖ ≤ q (some a) w.length)
    (hF : BoundedExpansionOn S A F U (s - k) (branchTermCount n s) (s + 1))
    (w : List (Coordinate n)) (hw : w.length ≤ μ) :
    ‖FullAmplitudePrimitiveBudget.jet w F x y η‖ ≤ branchJetConstant n s μ L K * H ^ (((s - k : ℕ) : ℝ) / s) := by
  have he := (hF.jet hU h w).mono (Nat.add_le_add_left hw _)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hw)) le_rfl
  exact he.norm_le_interpolated q hq hmono μ s (s - k) _ _ (Nat.sub_le _ _)
    L K H hL hK hH hlow hhigh hinterp x y η hpoint hA hS

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
    (x y η : Euclidean n) (hpoint : ((x, y), η) ∈ U)
    (hA : ∀ w, ‖FullAmplitudePrimitiveBudget.jet w A x y η‖ ≤ q none w.length)
    (hS : ∀ a w, ‖FullAmplitudePrimitiveBudget.jet w (scalarPrimitive S a) x y η‖ ≤ q (some a) w.length)
    (w : List (Coordinate n)) (hw : w.length ≤ μ) :
    ‖FullAmplitudePrimitiveBudget.jet w p.1 x y η‖ ≤ branchJetConstant n s μ L K *
      H ^ (((s - p.2.length : ℕ) : ℝ) / s) := by
  have he := (graph_branch_bounded_expansion hU h is p hp).mono
    (Nat.sub_le_sub_right his _) (branchTermCount_monotone n his) (Nat.add_le_add_right his 1)
  exact he.jet_norm_le_interpolated hU h q hq hmono
    μ s p.2.length L K H hL hK hH hlow hhigh hinterp x y η hpoint hA hS w hw

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
    (x y η : Euclidean n) (hpoint : ((x, y), η) ∈ U)
    (hA : ∀ w, ‖FullAmplitudePrimitiveBudget.jet w A x y η‖ ≤ q none w.length)
    (hS : ∀ a w, ‖FullAmplitudePrimitiveBudget.jet w (scalarPrimitive S a) x y η‖ ≤ q (some a) w.length)
    (w : List (Coordinate n)) (hw : w.length ≤ μ) :
    ‖FullAmplitudePrimitiveBudget.jet w p.1 x y η‖ ≤ branchJetConstant n s μ L K *
      H ^ (((s - p.2.length : ℕ) : ℝ) / s) := by
  have he := (adjoint_branch_bounded_expansion hU h is p hp).mono
    (Nat.sub_le_sub_right his _) (branchTermCount_monotone n his) (Nat.add_le_add_right his 1)
  exact he.jet_norm_le_interpolated hU h q hq hmono
    μ s p.2.length L K H hL hK hH hlow hhigh hinterp x y η hpoint hA hS w hw

end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local
