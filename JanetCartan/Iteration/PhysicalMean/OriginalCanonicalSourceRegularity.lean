module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourceInputIdentities
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import Lean

/-!
# Periodic regularity of the actual fixed-source inverse input

Consumer: the actual individual half-moment at order n+1, then the same final
wide-input Fourier mass (`app:ch_mean_pairs:eq:raw-adjoint-moments`,
`main:eq:primary-fixed-scales`). This applies the actual GLOBAL native39 Q0
regularity to the literal finite source. It is not the augmented-adjoint
regularity used to construct the auxiliary field, and selects no new inverse.
-/

set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalCanonicalSourceRegularity
private meta def exactTelescope (remaining : Nat) (type : Expr) (xs : Array Expr)
    (next : Array Expr → MetaM Unit) : MetaM Unit := do
  match remaining, type.consumeMData with
  | 0, _ => next xs
  | k+1, .forallE label domain body bi =>
    withLocalDeclNoLocalInstanceUpdate label bi domain fun x =>
      exactTelescope k (body.instantiate1 x) (xs.push x) next
  | _, _ => throwError "finite source original telescope changed"
run_meta do
  let run := `JanetCartan.PhysicalMean.OriginalCanonicalSource.iterate
  let current := `JanetCartan.PhysicalMean.OriginalCanonicalCurrent.Q0
  let native := `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.Q0
  let some body := (← getConstInfo current).value? | throwError "actual current lost its definition"
  exactTelescope 53 (← getConstInfo run).type #[] fun p => do
    let raw := (mkAppN body p[:50].toArray).headBeta
    unless raw.isAppOfArity native 39 do throwError "actual current is no longer literal global Q039"
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let e := mkAppN (mkConst run) p
    let toL2 := mkApp (mkConst `JanetCartan.CurrentMean.smoothResidualToL2) n
    let eL2 ← mkAppM ``DFunLike.coe #[toL2,e]
    withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s => do
      let hmem ← mkAppM `JanetCartan.CurrentMean.smoothResidualToL2_mem #[e,s]
      let proof := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.Q0_regular)
        (raw.getAppArgs ++ #[s,eL2,hmem])
      let named := mkAppN (mkConst current) p[:50].toArray
      let q ← mkAppM ``DFunLike.coe #[named,eL2]
      let target := (← inferType hmem).replace fun ex => if ex == eL2 then some q else none
      let ps := p.push s
      let type ← instantiateMVars (← mkForallFVars ps target)
      let value ← instantiateMVars (← mkLambdaFVars ps proof)
      let env ← getEnv
      for ex in #[type,value] do
        let missing := ex.getUsedConstants.filter (fun name => (env.find? name).isNone)
        unless missing.isEmpty do throwError "actual inverse regularity missing {missing.toList}"
        if ex.hasFVar || ex.hasMVar || ex.hasLevelMVar || ex.hasLooseBVars || ex.hasSorry then
          throwError "actual inverse regularity has an extra premise"
      unless type.getUsedConstants.contains current && type.getUsedConstants.contains run do
        throwError "actual inverse regularity lost the named original inverse or finite source"
      let name := `JanetCartan.PhysicalMean.OriginalCanonicalSource.iterate_inverse_regular
      addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
      addDocStringCore name "Every periodic Sobolev order of the SAME original global Q0 applied to the actual finite smooth source. No analytic premise, inverse reselection or augmented-adjoint substitution (app:ch_mean_pairs:eq:raw-adjoint-moments)."
      logInfo "actual finite Q0 source regularity checked at every order: native54, SAME global39 inverse"
end JanetCartan.PhysicalMean.OriginalCanonicalSourceRegularity
