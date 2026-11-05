module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourceRegularity
public import JanetCartan.Iteration.PhysicalMean.FixedPicardPrecisionSelection
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import Lean

/-!
# Specialize finite Picard deductions to the original named source

The original-data estimates remain producer obligations. This factory proves
only their direct consequence for the SAME selected run; it does not replace
an analytic producer by a successful-source record. Profile constants and
their nonnegativity certificates precede R0, reach, history, and the sample.
Consumer: `app:ch_mean_pairs:prop:mean-iteration` and the final input mass.
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.PhysicalMean.OriginalCanonicalPicardApplication
open Lean Meta Elab Command

private def sourceRoot := `JanetCartan.PhysicalMean.OriginalCanonicalSource
private def tail (e : Expr) (j : Nat) := Nat.repeat (fun x => Expr.proj ``And 1 x) j e
private def part (e : Expr) (j : Nat) := Expr.proj ``And 0 (tail e j)
private def app (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs
private def find (known : Array (Name × Expr)) (name : Name) : Option Expr :=
  (known.find? (fun pair => pair.1 == name)).map Prod.snd
private partial def telescope (remaining : Nat) (type : Expr) (xs : Array Expr)
    (next : Array Expr → MetaM Unit) : MetaM Unit := do
  match remaining,type.consumeMData with
  | 0,_ => next xs
  | k+1,.forallE label domain body bi =>
    withLocalDeclNoLocalInstanceUpdate label bi domain fun x =>
      telescope k (body.instantiate1 x) (xs.push x) next
  | _,_ => throwError "actual Picard deduction: original selected telescope changed"

/-- Specialize only the fixed data and scale certificates; retain exactly the
existing primitive estimate inputs, not any iterate-success proposition. -/
partial def applyKnownUntil (last : Name) (term type : Expr)
    (known : Array (Name × Expr)) (extras : Array Expr)
    (next : Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let .forallE label domain body bi := type.consumeMData
    | throwError "actual Picard deduction: generic primitive boundary {last} missing"
  let use (x : Expr) (more : Array Expr) : MetaM Unit := do
    let term := mkApp term x
    if label == last then next term more
    else applyKnownUntil last term (body.instantiate1 x) known more next
  if let some x := find known label then use x extras
  else if bi.isInstImplicit then
    if domain.isAppOf ``AddCommGroup then
      if let some x := find known `originalAddCommGroup then use x extras
      else use (← synthInstance domain) extras
    else if domain.isAppOf `Module then
      if let some x := find known `originalModule then use x extras
      else use (← synthInstance domain) extras
    else use (← synthInstance domain) extras
  else withLocalDeclNoLocalInstanceUpdate label bi domain fun x => use x (extras.push x)

private def save (name : Name) (params : Array Expr) (value target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let env ← getEnv
  for ex in #[type,value] do
    let missing := ex.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual Picard deduction missing {missing.toList}"
    if ex.hasFVar || ex.hasMVar || ex.hasLevelMVar || ex.hasLooseBVars || ex.hasSorry then
      throwError "actual Picard deduction has an unclosed parameter"
  let name := sourceRoot ++ name
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Conditional finite Picard deduction for the SAME named original source, global inverse, selected sample and fixed prefix. Exactly the primitive forcing/linear/quadratic estimates remain explicit; no iterate bound or successful source is assumed. Static profiles precede scale/history (app:ch_mean_pairs:prop:mean-iteration)."

/-- Open the original selected source and its unchanged history-scale facts.
The returned known dictionary contains only actual data/numeric certificates. -/
def withActualSelectedPicardData
    (next : Array Expr → Array (Name × Expr) → MetaM Unit) : MetaM Unit := do
  let run := sourceRoot ++ `selected_iterate
  telescope 51 (← getConstInfo run).type #[] fun p => do
    let xs := p[:50].toArray
    let ξ := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift xs
    let trial := xs ++ #[ξ,p[50]!]
    let n := app ``Nat.succ #[p[0]!]
    let some runBody := (← getConstInfo (sourceRoot ++ `iterate)).value?
      | throwError "actual Picard deduction lost the original run body"
    let originalRun := (mkAppN runBody (trial.push (mkNatLit 0))).headBeta
    unless originalRun.isAppOfArity ``sourceIterate 7 do
      throwError "actual Picard deduction changed the original source iteration"
    let runArgs := originalRun.getAppArgs
    let Y := runArgs[0]!
    let E := app (sourceRoot ++ `linear) trial
    let Q := app (sourceRoot ++ `quadratic) trial
    let g := app `JanetCartan.PhysicalMean.OriginalPeriodicBackground.forcing (xs.push ξ)
    let hInitial ← mkAppM ``le_trans
      #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS p[:44].toArray,p[45]!]
    let facts ← mkAppM ``fixedPicard_history_scale_facts #[hInitial,p[46]!]
    let R := app `JanetCartan.historyScale #[p[44]!,mkConst `JanetCartan.growthExponent,p[46]!]
    let T := app `JanetCartan.currentCoefficientScale #[p[44]!,p[46]!]
    let hh := part facts 3
    let htype ← inferType hh
    unless htype.isAppOfArity ``LE.le 4 do throwError "actual Picard source envelope changed"
    let h := htype.getAppArgs[3]!
    let known := #[(`n,n),(`Y,Y),(`originalAddCommGroup,runArgs[1]!),(`originalModule,runArgs[2]!),
      (`p,app ``residualSobolevSeminorm #[n]),(`E,E),(`Q,Q),(`g,g),
      (`m₀,app `JanetCartan.RevisedScales.baselineOrder #[n]),
      (`s₀,app `JanetCartan.RevisedScales.sourceOrder #[n]),(`T,T),(`R,R),(`h,h),
      (`hT,part facts 1),(`hR,part facts 0),(`hTR,part facts 2),(`hh,hh),(`hh1,part facts 4)]
    next p known

elab "construct_actual_canonical_picard_profile" : command => liftTermElabM do
  withActualSelectedPicardData fun p known => do
    let run := sourceRoot ++ `selected_iterate
    let E := (find known `E).get!
    let Q := (find known `Q).get!
    let g := (find known `g).get!
    let producer := ``sourceIterate_seminorm_profile
    let info ← getConstInfo producer
    let levels := info.levelParams.map (fun _ => Level.zero)
    let term := mkConst producer levels
    applyKnownUntil `hquadratic term (← inferType term) known #[] fun proof extras => do
      unless extras.size == 9 do
        throwError "actual Picard profile expected only Cg/CE/CQ, their nonnegativity and three primitive estimates"
      telescope 2 (← inferType proof) #[] fun orders => do
        let value := mkAppN proof orders
        let raw := mkAppN (mkConst ``sourceIterate [.zero])
          #[(find known `Y).get!, (find known `originalAddCommGroup).get!,
            (find known `originalModule).get!,E,Q,g,orders[0]!]
        let actual := app run (p.push orders[0]!)
        let target := (← inferType value).replace fun ex => if ex == raw then some actual else none
        unless target.getUsedConstants.contains run do
          throwError "actual finite profile lost its named selected source"
        let params := p[:44].toArray ++ extras[:6].toArray ++ p[44:].toArray ++
          extras[6:].toArray ++ orders
        save `selected_iterate_profile_of_primitive_profiles params value target
        logInfo "actual selected finite profile: static coefficients BEFORE scale/history; SAME iterate52, ONE shift and fixed L; three primitive estimates remain conditional"

end JanetCartan.PhysicalMean.OriginalCanonicalPicardApplication
end
