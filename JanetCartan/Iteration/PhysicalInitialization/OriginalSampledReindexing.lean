module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledObserved
public meta import Lean

/-!
# Uniform original signed costs after source-label reindexing

These are the individual bounds consumed by the actual observed-chain
application (`app:ch_regular:lem:finite-chain`). The map of source labels
changes neither the history, frequency nor slow scale. In particular this
is a pullback of one uniform estimate on the whole admitted family, not an
estimate on a newly chosen representative history.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalInitialization.OriginalSampledReindexing
open Lean Meta Elab Command OriginalProtectedTemplate
open scoped Matrix.Norms.Frobenius
private def root := `JanetCartan.PhysicalInitialization.OriginalSampledReindexing
private def obs := `JanetCartan.PhysicalInitialization.OriginalSampledObserved
private def poly := `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def a (k : Name) (x : Array Expr) := mkAppN (mkConst k) x

run_cmd liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (reg ++ `Graph.S)).type (some 34) fun g _ => do
    let d := g[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let I := a (poly ++ `GraphFamily) g
    withLocalDeclD `β (mkSort .one) fun β => do
     withLocalDeclD `indices (← mkArrow β I) fun e => do
      forallBoundedTelescope (← inferType (a (poly ++ `graph_signed_costs) g)) (some 3) fun signs _ => do
       unless signs.size == 3 do throwError "changed signed-factor orientation spine"
       let p := g ++ #[β,e] ++ signs
       withLocalDeclD `j β fun j => do
        let i := mkApp e j
        let raw := Expr.proj ``Subtype 0 i
        let ρ ← mkLambdaFVars #[j] (a `JanetCartan.PhysicalPrimary.OriginalHistoryFamily.RawIndex.lam #[d,mkConst ``Unit,raw])
        let low := .proj ``And 0 (mkApp (a (poly ++ `graph_signed_low) (g ++ signs)) i)
        let t ← inferType low
        unless t.getAppArgs.size ≥ 2 do throwError "changed actual raw norm bound"
        let T := t.getAppArgs[t.getAppArgs.size-2]!.appArg!
        let operators ← store (root ++ `operator) p (← mkLambdaFVars #[j] T) true
        let hT ← store (root ++ `raw_bound) p (← mkLambdaFVars #[j] low)
        let hC := mkApp (a `JanetCartan.PhysicalInitialization.OriginalSampledOperatorBounds.Low.fact0 g[:23].toArray) signs[0]!
        let C := (← inferType hC).appArg!
        discard <| store (root ++ `low) p (a (obs ++ `uniform_low_cost) #[d,n,β,C,hC,ρ,operators,hT])
        let hc := a (poly ++ `graph_signed_costs) (g ++ signs)
        let originalType ← inferType hc
        let pa := originalType.getAppArgs
        unless pa.size == 11 do throwError "changed polynomial-cost parameter spine: {pa.size}"
        let key := poly ++ `pullback_cost
        let info ← getConstInfo key
        let pulled := mkAppN (mkConst key (info.levelParams.map fun _ => .zero))
          (#[pa[0]!,β] ++ pa[1:].toArray ++ #[e,hc])
        let resultType ← inferType pulled
        discard <| store (root ++ `local_operator) p resultType.getAppArgs.back! true
        discard <| store (root ++ `costs) p pulled
end JanetCartan.PhysicalInitialization.OriginalSampledReindexing
end
