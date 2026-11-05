module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSampledTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
public meta import Lean

/-!
# Retain the same native50 outer sample for the actual mean fields

Read the single original existential shift type, extended shift, sample index,
and literal finite-index instance from the actual event. This is an application
of the already fixed event, not another selection or sampling-success premise.
The row's original outer B/psi are exactly those used by the actual A52 producer
(`app:ch_mean_pairs:defn:mean-canonical`).
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.PhysicalMean.OriginalCanonicalSampledApplication
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate

private def root := `JanetCartan.PhysicalMean.OriginalCanonicalSampled

/-- The event's exact native50, its single original shift parameter, original
SampleIndex7 arguments, finite-band count, and literal original Fintype. This
read-only metadata view does not choose a shift or a finite-index instance. -/
def withActualSample
    (next : Array Expr → Expr → Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  withTransparency .reducible <| withActualRow fun d => do
    let xs := d.parameters[:50].toArray
    let event := mkAppN (mkConst
      `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.exists_on_original_history) xs
    let result ← inferType event
    let some bare := result.find? (·.isAppOfArity
      `JanetCartan.PhysicalSampling.OriginalScalarFamily.kernel 46)
      | throwError "actual sampled fields: original scalar46 missing"
    let J := bare.getAppArgs[43]!
    let existsType ← whnf result
    unless existsType.isAppOfArity ``Exists 2 do
      throwError "actual sampled fields: original single shift type changed"
    let .lam label domain body bi := existsType.getAppArgs[1]!.consumeMData
      | throwError "actual sampled fields: original shift predicate changed"
    withLocalDeclNoLocalInstanceUpdate label bi domain fun ξ => do
      let body := body.instantiate1 ξ
      let some si := body.find? (·.isAppOfArity
        `JanetCartan.CanonicalRowComparison.SampleIndex 7)
        | throwError "actual sampled fields: original SampleIndex7 missing"
      let some deviation := body.find? (·.isAppOfArity
        `JanetCartan.Sampling.Realization.familyDeviation 17)
        | throwError "actual sampled fields: original familyDeviation17 missing"
      let some fI ← deviation.getAppArgs.findM? (fun arg => do
        if arg.hasLooseBVars then return false
        return (← inferType arg).isAppOfArity ``Fintype 1)
        | throwError "actual sampled fields: original finite-index instance missing"
      unless ← isDefEq (← inferType fI).getAppArgs[0]! si.getAppArgs[0]! do
        throwError "actual sampled fields: changed original finite index"
      next xs ξ si.getAppArgs J fI

private def applyKnown (name : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let info ← getConstInfo name
  let head := mkConst name (info.levelParams.map (fun _ => Level.zero))
  let rec count : Expr → Nat
    | .forallE _ _ body _ => 1 + count body
    | .mdata _ body => count body
    | _ => 0
  let rec go (fuel : Nat) (type : Expr) (args : Array Expr) : MetaM Expr := do
    match fuel, type.consumeMData with
    | remaining + 1, .forallE label _ body _ =>
      let key := label.eraseMacroScopes
      if let some value := (known.find? (fun pair => pair.1 == key)).map Prod.snd then
        go remaining (body.instantiate1 value) (args.push value)
      else if key == `i then
        pure (mkAppN head args)
      else
        throwError "actual sampled fields: missing exact argument {name}.{key}"
    | _, _ => pure (mkAppN head args)
  let type := info.type
  go (count type) type #[]

private def save (name : Name) (params : Array Expr) (term : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params (← inferType term))
  let value ← instantiateMVars (← mkLambdaFVars params term)
  let env ← getEnv
  for closed in #[type,value] do
    let missing := closed.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "actual sampled fields: missing producer constants {missing.toList}"
  if type.hasFVar || type.hasMVar || type.hasLevelMVar || type.hasLooseBVars || type.hasSorry ||
      value.hasFVar || value.hasMVar || value.hasLevelMVar || value.hasLooseBVars || value.hasSorry then
    throwError "actual sampled fields: open or newly selected field {name}"
  let name := root ++ name
  addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  addDocStringCore name "The SAME original native50 event and extended shift, outer SampleIndex, unscaled positive baseline and unrenormalized full-angular derivative (app:ch_mean_pairs:defn:mean-canonical)."
  logInfo m!"actual sampled field {name}: native{params.size}, SAME original outer index/color/node and shift"

elab "construct_actual_canonical_sampled " mode:num : command => liftTermElabM do
  withActualSample fun xs ξ sa J _ => do
    let I := sa[0]!
    unless I.isAppOfArity `JanetCartan.PhysicalSampling.OriginalWeights.Index 22 do
      throwError "actual sampled fields: missing original static22 index"
    let fixed := I.getAppArgs
    let outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
    let B := mkAppN (mkConst (outer ++ `B)) fixed
    let ψ := mkAppN (mkConst (outer ++ `ψ)) fixed
    let n := mkApp (mkConst ``Nat.succ) xs[0]!
    let N := mkApp (mkConst `JanetCartan.embeddingDimension) n
    let base := mkAppN (mkConst
      `JanetCartan.PhysicalMean.OriginalCanonicalBaseline.positiveBaseline) xs
    let G := mkAppN (mkConst
      `JanetCartan.PhysicalMean.OriginalCanonicalActual.G) xs
    let known := #[(`ι,I),(`n,n),(`N,N),(`J,J),(`p,sa[1]!),
      (`B,B),(`ψ,ψ),(`w,sa[4]!),(`h,sa[5]!),(`U,sa[6]!),(`base,base),(`G,G)]
    let params := xs.push ξ
    unless params.size == 51 do throwError "actual sampled fields: changed original shift51"
    match mode.getNat with
    | 0 => save `base params (← applyKnown (root ++ `sampledPositiveBaseline) known)
    | 1 => save `G params (← applyKnown (root ++ `sampledDerivative) known)
    | 2 => withLocalDeclNoLocalInstanceUpdate `L .default (mkConst ``Nat) fun L => do
      save `Gprefix (params.push L)
        (← applyKnown (root ++ `sampledPrefixDerivative) (known.push (`L,L)))
    | _ => throwError "actual sampled fields: unknown publication stage"

end JanetCartan.PhysicalMean.OriginalCanonicalSampledApplication
end
