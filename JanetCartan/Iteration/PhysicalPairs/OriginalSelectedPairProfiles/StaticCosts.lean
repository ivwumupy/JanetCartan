module

public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedNodeAdmission
public import JanetCartan.Iteration.PhysicalPairs.OriginalUniformStageLag
public import JanetCartan.Iteration.PhysicalPairs.OriginalUniformStageSize
public meta import Lean

/-!
# Original signed costs before the dynamic estimate leaf

`OriginalStepEstimates.C_of_primary_strain` only needs the early coefficients.
Read their literal operands from the already proved original complete-node
ledger, then use the existing source-uniform lag and size constants. This
introduces no mathematical declaration, witness or hypothesis. The later
application of the actual estimates must still check these expressions against
the named `Clag` and `Csize` definitions (`main:thm:step`,
`main:eq:pair-error`, `main:eq:pair-high-size`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPairs.OriginalSelectedPairProfiles.StaticCosts

open Lean Meta

private def profiles := `JanetCartan.PhysicalPairs.OriginalSelectedCompleteProfiles
private def lag := `JanetCartan.PhysicalPairs.OriginalUniformStageLag
private def size := `JanetCartan.PhysicalPairs.OriginalUniformStageSize
private def selection := `JanetCartan.PhysicalPairs.OriginalUniformSizeSelection
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p

private def replaceStatic (p : Array Expr) (cap : Expr)
    (selected33 : Array Expr) (count Cscale hcap value : Expr) : MetaM Expr := do
  let oldArgs := p[:33].toArray ++ #[p[53]!,p[54]!,cap]
  let newArgs := selected33 ++ #[count,Cscale,hcap]
  let result := value.replaceFVars oldArgs newArgs
  for binder in p.push cap do
    if result.containsFVar binder.fvarId! then
      throwError "actual early signed costs: later history, target, source or gate escaped"
  if result.hasMVar || result.hasLevelMVar || result.hasLooseBVars || result.hasSorry then
    throwError "actual early signed costs: unresolved original scalar expression"
  let env ← getEnv
  let missing := result.getUsedConstants.filter (fun n => (env.find? n).isNone)
  unless missing.isEmpty do
    throwError "actual early signed costs: missing original metadata {missing.toList}"
  return result

/-- Return the SAME raw lag function, its all-order nonnegativity proof,
the SAME raw size function, and its all-order nonnegativity proof, in that
order. Each function has domain `ℕ`. Only the original selected33, Picard
count, fixed pair scale and numerical history-cap proof are substituted.
All history/target/sample/gate variables of the actual node ledger are
rejected from the output. No new scalar alias or successful estimate is
introduced (`main:thm:step`; consumer `C_of_primary_strain`). -/
def rawCosts (selected33 : Array Expr) (count Cscale hcap : Expr) :
    MetaM (Expr × Expr × Expr × Expr) := do
  unless selected33.size == 33 do
    throwError "actual early signed costs: original selected33 changed"
  forallBoundedTelescope (← getConstInfo (profiles ++ `nodeJets)).type (some 56) fun p ledger => do
    unless p.size == 56 &&
        ledger.isAppOfArity `JanetCartan.PhysicalPairs.OriginalSelectedWaves.nodeJets 8 do
      throwError "actual early signed costs: original complete-node ledger56 changed"
    let a := ledger.getAppArgs
    let C := a[4]!
    let theta := a[6]!
    let W := a[7]!
    unless theta.isAppOfArity `JanetCartan.PhysicalPairs.OriginalStageMetric.angles 45 &&
        W.isLambda && W.bindingBody!.isAppOfArity `JanetCartan.PhysicalPairs.OriginalSourceSchwartz.wave 53 do
      throwError "actual early signed costs: different original wave family or phase"
    unless C == app (profiles ++ `Camplitude) (p[:33].toArray.push p[53]!) do
      throwError "actual early signed costs: complete amplitude price is no longer static33+N"
    let b := theta.getAppArgs[:37].toArray
    let hC := app (profiles ++ `Camplitude_nonneg) (p[:33].toArray.push p[53]!)
    let capType := (← inferType (app (selection ++ `native_budget) b)).bindingDomain!
    withLocalDeclNoLocalInstanceUpdate `historyCoversSize .default capType fun cap => do
      let (Cpair,hCpair) ←
        withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
          let pre := b ++ #[C,hC,q]
          return (← mkLambdaFVars #[q] (app (lag ++ `constant) pre),
            ← mkLambdaFVars #[q] (app (lag ++ `constant_nonneg) pre))
      let pre := b ++ #[cap,C,hC]
      let (CS,hCS) ←
        withLocalDeclNoLocalInstanceUpdate `r .default (mkConst ``Nat) fun r => do
          let args := pre.push r
          let named := app (size ++ `constant) args
          let raw := (((← getConstInfo (size ++ `constant)).value! (allowOpaque := true)).beta args).headBeta
          unless raw.isAppOfArity `JanetCartan.PhysicalPairs.OriginalStageSize.cost 2 do
            throwError "actual early signed costs: original size-cost formula changed"
          let cost := raw.getAppArgs
          let nonneg := app `JanetCartan.PhysicalPairs.OriginalStageSize.cost_nonneg
            #[cost[0]!,cost[1]!,mkApp (app (selection ++ `D_nonneg) pre) r]
          return (← mkLambdaFVars #[r] named, ← mkLambdaFVars #[r] nonneg)
      return (← replaceStatic p cap selected33 count Cscale hcap Cpair,
        ← replaceStatic p cap selected33 count Cscale hcap hCpair,
        ← replaceStatic p cap selected33 count Cscale hcap CS,
        ← replaceStatic p cap selected33 count Cscale hcap hCS)

end JanetCartan.PhysicalPairs.OriginalSelectedPairProfiles.StaticCosts
end
