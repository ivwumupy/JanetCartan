module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSignedSum
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampleBudgets

/-! # Exact coefficient mass for the actual common-shift signed sum

The bound is fixed before the initial scale, history, shift and pair. The
weights below are the SAME original extended-shift weights of the Schwartz
sum and of the primary, not probability surrogates. `main:eq:sampling`,
`app:ch_pairs:eq:pairs-lag-sum-error`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators
namespace JanetCartan.PhysicalPairs.OriginalSampleMass
open PhysicalSampling CanonicalRowComparison SeparatedSampling SamplingKernelBounds
variable {J : Type} [Fintype J]
def price (p : ℕ) (B : ℝ) (P : J → ℝ) := ((Fintype.card J : ℝ)*countConstant p B) * (countConstant p B * (∑ j, P j))

theorem price_spec (p : ℕ) (B : ℝ) (ψ : J → Point → ℝ) (P : J → ℝ) (R : ℝ) (ξ : J → Lattice → Point)
    (hp : 0 < p) (hB : 0 ≤ B) (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hR : 1 ≤ R) :
    let μ := OriginalSignedSum.trueWeight p B ψ R ξ
    0 ≤ price p B P ∧ ProductSum.coefficientMass μ ≤ price p B P * R^(1+samplingSlack) ∧
    (∑ i, Real.sqrt (μ i)) ≤ Real.sqrt (price p B P) * R^((1+samplingSlack)/2) := by
  have h := UniformStep.sampled_weight_budgets_originalScale p hB (OriginalWindow.window_bounds hp) hψ hR ξ
  simpa only [price,OriginalSignedSum.trueWeight,one_pow,mul_one] using
    And.intro (mul_nonneg h.1 h.2.1) h.2.2.2.2.2
end JanetCartan.PhysicalPairs.OriginalSampleMass
end
public meta section
set_option maxHeartbeats 750000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalSampleMass
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSampleMass
private def src := `JanetCartan.PhysicalPairs.OriginalSignedSum
private def outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
elab "price_actual_signed_sum_weights " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (hist ++ `index)).type (some 49) fun p _ => do
    let stem := p[:45].toArray
    let stat := p[:22].toArray
    let μ := a (src ++ `weight) stem
    let actual := ((← getConstInfo (src ++ `weight)).value! (allowOpaque := true)).beta stem
    let wa := actual.getAppArgs
    unless actual.isAppOfArity (src ++ `trueWeight) 6 do throwError "source sum lost its unchanged extended-shift weights"
    let raw := ((← getConstInfo (outer ++ `Index)).value! (allowOpaque := true)).beta stat
    let fi ← synthInstance (mkApp (mkConst ``Fintype [.zero]) raw)
    let hψ := a (outer ++ `patchBounds) stat
    let P ← forallBoundedTelescope (← inferType hψ) (some 1) fun ys t => mkLambdaFVars ys t.appArg!
    let cost := a (ns ++ `price) #[wa[0]!,fi,wa[1]!,wa[2]!,P]
    if piece.getNat == 0 then
      discard <| store (ns ++ `constant) stat cost true
      return
    let some pair := (← inferType (a (hist ++ `native_window) p)).find? (fun e => e.isAppOfArity `JanetCartan.PhysicalInitialization.OriginalSampledPairs.pair 30)
      | throwError "missing native original historyScale"
    let rt := pair.getAppArgs
    let bpos ← mkAppM ``le_of_lt #[a (outer ++ `hB) stat]
    let pf := a (ns ++ `price_spec) #[wa[0]!,fi,wa[1]!,wa[2]!,wa[3]!,P,wa[4]!,wa[5]!,p[43]!,bpos,hψ,rt[24]!]
    let t ← whnfR (← inferType pf)
    let target := t.replace fun e => if e == cost then some (a (ns ++ `constant) stat) else if e == actual then some μ else none
    discard <| store (ns ++ `coefficient_budgets) stem pf false (some target)
price_actual_signed_sum_weights 0
price_actual_signed_sum_weights 1
end JanetCartan.PhysicalPairs.OriginalSampleMass
end
