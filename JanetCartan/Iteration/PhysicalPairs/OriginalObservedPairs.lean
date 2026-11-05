module
public import JanetCartan.Iteration.PhysicalPairs.OriginalFirstMask
public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledChains

/-! # Every actually measured signed source in the complete original chain

The complete signed source label is retained even when several labels map to
one operator history. Supply its true complete-wave derivative profile once;
all support, polynomial source cost, first mask and individual factor estimates
are now deductions, not premises. The observed residual powers are on the
original norm ball and the SAME complete signs/coefficients. Consumer:
`app:ch_regular:eq:finite-expansion`, `main:prop:pairs`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalObservedPairs

theorem flat_price {β H : Type} [NormedAddCommGroup H] (u : β → H) (ρ : β → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (h : ∀ t, ‖u t‖ ≤ D) : ∃ C a : ℝ, 0 ≤ C ∧ ∀ t, ‖u t‖ ≤ C*1*(ρ t)^a :=
  ⟨D,0,hD,fun t ↦ by simpa only [Real.rpow_zero,mul_one] using h t⟩
end JanetCartan.PhysicalPairs.OriginalObservedPairs
end

public meta section
set_option maxHeartbeats 900000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalObservedPairs
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalObservedPairs
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def cost := `JanetCartan.PhysicalPairs.MeasuredSourceCost
private def chain := `JanetCartan.PhysicalInitialization.OriginalSampledChains
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
elab "consume_original_observed_pairs " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (fm ++ `first_mask)).type (some 41) fun p _ => do
    let base := p[:37].toArray
    let sampled := p[:38].toArray
    let cData := base ++ p[38:40].toArray
    let β := a (hist ++ `Labels) base
    let e := a (hist ++ `historyMap) base
    let u := a (fm ++ `measured) sampled
    if piece.getNat == 0 then
      let raw := ((← getConstInfo (fm ++ `measured)).value! (allowOpaque := true)).beta sampled
      lambdaBoundedTelescope raw 1 fun t body => do
        unless body.isAppOfArity `JanetCartan.PhysicalPairs.OriginalSignedData.measured 50 do throwError "changed actual original uncut source slot"
        let pf ← mkLambdaFVars t (a (cost ++ `native_support) body.getAppArgs)
        discard <| store (ns ++ `support) sampled pf
      return
    if piece.getNat == 1 then
      let hu ← withLocalDeclD `signedLabel β fun t => mkLambdaFVars #[t] (.proj ``And 0 (mkApp (a (fm ++ `norms) p) t))
      let pf ← mkAppM (ns ++ `flat_price) #[u,a (fm ++ `frequency) base,a (fm ++ `sourceNormCost) cData,a (fm ++ `sourceNormCost_nonneg) cData,hu]
      discard <| store (ns ++ `source_polynomial) p pf
      return
    let proof := a (chain ++ `observed_residual_powers) (p[:36].toArray ++ #[β,e,u,a (ns ++ `support) sampled,a (ns ++ `source_polynomial) p])
    forallBoundedTelescope (← inferType proof) (some 2) fun obs _ => do
      unless obs.size == 2 do throwError "actual chain lost the output observation set and measurability"
      let actual := mkAppN proof (obs.push (a (fm ++ `first_mask) p))
      discard <| store (ns ++ `observed_powers) (p ++ obs) actual
consume_original_observed_pairs 0
consume_original_observed_pairs 1
consume_original_observed_pairs 2
end JanetCartan.PhysicalPairs.OriginalObservedPairs
end
