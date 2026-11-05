module
public import JanetCartan.Iteration.PhysicalPairs.OriginalStageSize
public import JanetCartan.Iteration.PhysicalPairs.OriginalStageMetric

/-! # Common-stage original metric lag, Sobolev sizes and displacement

The genuine physical correction is the same explicitly weighted finite sum in
all three estimates. On the shared actual stage the data go through the same
external ξ and full family of Schwartz waves. First cap the freely chosen raw
frame width, and choose the finite history reserve once, before any sample or
history. No success estimate for a signed response is among the inputs.
`main:prop:pairs`, `main:eq:self-off`, `main:eq:joint-physical-profile`.
-/
public meta section
set_option maxHeartbeats 1600000
set_option maxRecDepth 18000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalPairStage
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalPairStage
private def sel := `JanetCartan.PhysicalPairs.OriginalSizeSelection
private def stat := `JanetCartan.PhysicalPairs.OriginalStageSize
private def metric := `JanetCartan.PhysicalPairs.OriginalStageMetric
private def width := `JanetCartan.PhysicalPairs.OriginalStageLagWidth
private def a (k : Name) (v : Array Expr) := mkAppN (mkConst k) v
run_cmd liftTermElabM do
  forallBoundedTelescope (← getConstInfo (stat ++ `physicalL2)).type (some 51) fun p _ => do
    let b := p[:37].toArray
    let hcap := p[37]!
    let selection := b ++ #[hcap,p[39]!,p[40]!]
    let hwidthType := (← inferType (a (metric ++ `lag) b)).bindingDomain!
    withLocalDeclD `chosenWidthMargin hwidthType fun hγ => withLocalDeclD `accuracy (mkConst ``Nat) fun q => do
      let hr ← mkAppM ``le_trans #[a (sel ++ `reaches_signed) selection,p[43]!]
      let lag := a (metric ++ `lag) (b ++ #[hγ] ++ p[38:42].toArray ++ #[q,p[42]!,hr] ++ p[44:].toArray)
      let sizes ← withLocalDeclD `order (mkConst ``Nat) fun s => mkLambdaFVars #[s] (a (stat ++ `size) (p[:42].toArray ++ #[s] ++ p[42:].toArray))
      let out ← mkAppM ``And.intro #[lag,← mkAppM ``And.intro #[sizes,a (stat ++ `physicalL2) p]]
      discard <| store (ns ++ `at_shared_history) (b ++ #[hγ,hcap] ++ p[38:42].toArray ++ #[q] ++ p[42:].toArray) out

private partial def capInputs (i capIndex : Nat) (raw : Expr) (pars vals : Array Expr) (g c : Option Expr) : MetaM Unit := do
  if i == 37 then
    let some g := g | throwError "lost the actual pre-source frame width"
    let some c := c | throwError "lost the earlier finite history cap"
    let n := mkApp (mkConst ``Nat.succ) vals[0]!
    let hγ := a (width ++ `width_le_frame) #[n,vals[1]!,g]
    let hcap := a (sel ++ `covers_size) #[vals[0]!,c]
    let final := mkAppN raw #[hγ,hcap]
    discard <| store (ns ++ `estimates) pars final
    return
  let ty ← whnfR (← inferType raw)
  unless ty.isForall do throwError "early original graph cut off at {i}"
  let dom := ty.bindingDomain!
  let n := if vals.isEmpty then mkNatLit 0 else mkApp (mkConst ``Nat.succ) vals[0]!
  if i == 24 then
    withLocalDeclD `outerGraphWidth dom fun z => do
      let x := a (width ++ `width) #[n,vals[1]!,z]
      capInputs (i+1) capIndex (mkApp raw x) (pars.push z) (vals.push x) (some z) c
  else if i == 25 then
    let some z := g | throwError "missing free outer graph width"
    let t := dom.replace fun e => if e == vals[24]! then some z else none
    withLocalDeclD `outerGraphWidth_pos t fun hz => do
      let x := a (width ++ `width_pos) #[n,vals[1]!,z,hz]
      capInputs (i+1) capIndex (mkApp raw x) (pars.push hz) (vals.push x) g c
  else if i == capIndex then
    withLocalDeclD `earlierFiniteOrder dom fun m => do
      let x := a (sel ++ `historyCap) #[vals[0]!,m]
      capInputs (i+1) capIndex (mkApp raw x) (pars.push m) (vals.push x) g (some m)
  else
    withLocalDecl ty.bindingName! ty.bindingInfo! dom fun x =>
      capInputs (i+1) capIndex (mkApp raw x) (pars.push x) (vals.push x) g c
run_cmd liftTermElabM do
  let key := ns ++ `at_shared_history
  let idx ← forallBoundedTelescope (← getConstInfo key).type (some 39) fun p _ => do
    let cap := (← inferType p[38]!).appArg!
    let i := p.toList.idxOf cap
    unless i < 37 && i != 24 && i != 25 do throwError "the native rStar is not a free prehistory input ({i})"
    return i
  capInputs 0 idx (mkConst key) #[] #[] none none
  logInfo m!"Identical Schwartz correction in lag, H^s and L²; the existing frame and the true strong-coefficient history are reached by choosing numerical graph binder 24 and history cap {idx} before all histories."
end JanetCartan.PhysicalPairs.OriginalPairStage
end
