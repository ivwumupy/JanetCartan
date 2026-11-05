module
public import JanetCartan.Iteration.PhysicalPairs.OriginalObservationBuffer
public import JanetCartan.Iteration.PhysicalPairs.ObservedSchwartz
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalProfiles
/-! # Smooth the same complete source wave on its existing selected cell

The full-angular field already has its zero-safe selected-cell theorem. For
its unscaled positive baseline, use the ENTIRE outer parameter window and the
same original doubled product cell, then the same Graph42 response. There is
no inner-factor premise. This supplies the actual ψ-Schwartz producer, not an
R-bound or a changed physical primary (`app:ch_pairs:lem:pairs-ledger`).
-/
public meta section
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSelectedCellTemplate
open Lean Meta Elab Command
open PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSelectedCell
private def wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def obs := `JanetCartan.PhysicalPairs.OriginalObservationBuffer
private def app (key : Name) (args : Array Expr) := mkAppN (mkConst key) args
private def body (key : Name) (p : Array Expr) : MetaM Expr := do
  return ((← getConstInfo key).value! (allowOpaque := true)).beta p
private def argument (e : Expr) (key : Name) : MetaM Expr := do
  let mut type := (← getConstInfo e.getAppFn.constName!).type
  for v in e.getAppArgs do
    unless type.isForall do throwError "selected-cell source: changed native argument telescope"
    if type.bindingName! == key then return v
    type := type.bindingBody!.instantiate1 v
  throwError "selected-cell source: missing original argument {key}"
private def subtypeSource (h : Expr) : MetaM Expr := do
  let t ← inferType h
  unless t.isAppOfArity ``Membership.mem 5 do throwError "selected-cell source: missing original real source admission"
  return mkAppN (mkConst ``Subtype.mk [.succ .zero])
    #[t.getAppArgs[0]!,t.appFn!,t.appArg!,h]
private def smoothMono (h target subset : Expr) : MetaM Expr := do
  let type ← inferType h
  unless type.isAppOfArity ``ContDiffOn 11 do
    throwError "selected-cell source: changed actual response smoothness signature"
  let a := type.getAppArgs
  return mkAppN (mkConst ``ContDiffOn.mono type.getAppFn.constLevels!)
    (a[:8].toArray ++ #[a[10]!,a[9]!,a[8]!,h,target,subset])
private def save (key : Name) (p : Array Expr) (type value : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p type)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars || e.hasSorry then
      throwError "selected-cell source: unresolved field {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  liftM <| IO.eprintln s!"selected-cell source: kernel checking {name}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  liftM <| IO.eprintln s!"selected-cell source: kernel passed {name}"

elab "publish_original_selected_cell_smooth " which:num : command => liftTermElabM do
  unless which.getNat < 2 do throwError "selected-cell source: unknown mode"
  withActualSelectedSourceWave fun p _ _ literal oldSmooth native64 _ => do
    unless literal.isAppOfArity (wave ++ `Combined.field) 69 &&
        oldSmooth.isAppOfArity (wave ++ `Combined.active_smooth) 70 do
      throwError "selected-cell source: actual combined field/smoothness changed"
    let ca := literal.getAppArgs
    let combined ← body (wave ++ `Combined.field) ca
    unless combined.isAppOfArity ``HAdd.hAdd 6 do throwError "selected-cell source: combined wave is not baseline PLUS whole-angular"
    let baseline := combined.getAppArgs[4]!
    let angular := combined.getAppArgs[5]!
    unless baseline.isAppOfArity (wave ++ `Corrected.unrestricted_atom) 62 &&
        angular.isAppOfArity (wave ++ `Whole.full_angular.corrected) 66 do
      throwError "selected-cell source: native parent or whole-angular ABI changed"
    let atom ← body baseline.getAppFn.constName! baseline.getAppArgs
    let T ← argument atom `T
    unless T.isAppOfArity (wave ++ `T) 53 do throwError "selected-cell source: literal source53 changed"
    let source := T.getAppArgs
    liftM <| IO.eprintln "selected-cell: decoded actual source53"
    let n ← argument atom `n
    let c := baseline.appArg!
    let outer := app (geo ++ `outer_weight_parameter)
      (source ++ ca[64:68].toArray ++ #[oldSmooth.getAppArgs[68]!])
    let outerType ← Core.betaReduce (← zetaReduce (← inferType outer))
    unless outerType.isAppOfArity ``Membership.mem 5 do
      throwError "selected-cell source: actual outer parameter admission changed"
    let bp := p[:50].toArray.push p[52]!
    let buffer ← body (obs ++ `statement) bp
    unless buffer.isAppOfArity ``And 2 do throwError "selected-cell source: original buffer certificate changed"
    let X := buffer.getAppArgs[0]!.appArg!
    unless X.isAppOfArity `Metric.ball 4 do throwError "selected-cell source: original selected cell is not its literal ball"
    let current := app (geo ++ `current_cell) source
    let ct := (← inferType current).getAppArgs
    let cell := ct[ct.size-2]!
    unless cell.isAppOfArity `Metric.closedBall 4 do throwError "selected-cell source: original closed doubled cell changed"
    let center ← mkAppM ``Prod.snd #[cell.getAppArgs[2]!]
    liftM <| IO.eprintln "selected-cell: original buffer and doubled cell decoded"
    let hp := app ``JanetCartan.PhysicalPairs.ObservedSchwartz.doubled_product
      #[n,center,X.getAppArgs[3]!]
    let ptype := (← inferType hp).getAppArgs
    let hp := mkAppN (mkConst ``Set.Subset.trans [.zero])
      #[cell.getAppArgs[0]!,ptype[ptype.size-2]!,cell,ct.back!,hp,current]
    let V := outerType.getAppArgs[3]!
    let hspace := app ``JanetCartan.PhysicalPairs.ObservedSchwartz.slice_in_space
      #[n,X,← argument atom `U,V,ct.back!,app (geo ++ `current_space) source,hp,c,outer]
    liftM <| IO.eprintln "selected-cell: outer product and current space assembled"
    let rawSmooth := app (wave ++ `joint_raw_smooth) source
    let rawType ← inferType rawSmooth
    unless rawType.isAppOfArity ``ContDiffOn 11 do
      throwError "selected-cell source: changed actual joint raw smoothness"
    let N ← argument atom `N
    let hraw := app (geo ++ `contDiffOn_slice)
      #[n,N,X,V,rawType.getAppArgs[10]!,rawType.getAppArgs[9]!,rawSmooth,hp,c,outer]
    liftM <| IO.eprintln "selected-cell: raw smooth slice assembled"
    let quads := app (wave ++ `source_quadratures) (source ++ #[c,outer])
    let re ← subtypeSource (.proj ``And 0 quads)
    let im ← subtypeSource (.proj ``And 1 quads)
    liftM <| IO.eprintln "selected-cell: actual real quadrature sources assembled"
    let graphSmooth := app `JanetCartan.PhysicalSampling.OriginalGraphResponse.smoothOn native64[:42].toArray
    let hre ← smoothMono (mkApp graphSmooth re) X hspace
    let him ← smoothMono (mkApp graphSmooth im) X hspace
    liftM <| IO.eprintln "selected-cell: actual Graph42 response restricted"
    let src := app (wave ++ `source) (source ++ #[c,outer])
    let hresponse := app (wave ++ `contDiffOn_complexifyResponse)
      #[n,N,← argument atom `B,src,X,hre,him]
    let hbase ← mkAppM ``ContDiffOn.sub #[hraw,hresponse]
    liftM <| IO.eprintln "selected-cell: unscaled baseline smoothed on actual buffer"
    let hang := app (wave ++ `Whole.full_angular_smooth_on_selected_cell.corrected) angular.getAppArgs
    let proof ← mkAppM ``ContDiffOn.add #[hbase,hang]
    let smoothType ← inferType proof
    unless smoothType.isAppOfArity ``ContDiffOn 11 do throwError "selected-cell source: complete-wave smoothness changed"
    let named := app ``JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourceCombinedWave p
    let target := mkAppN smoothType.getAppFn (smoothType.getAppArgs.set! 9 named)
    if which.getNat == 0 then
      save `statement p (mkSort .zero) target true
    else
      save `smooth p (app (ns ++ `statement) p) proof
end JanetCartan.PhysicalPairs.OriginalSelectedCellTemplate
end
