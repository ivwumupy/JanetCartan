module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPrimarySourceGeometry
public import JanetCartan.Iteration.PhysicalPairs.SampledQuadrature
import all JanetCartan.Iteration.PhysicalInitialization.OriginalSampledPairs
import all JanetCartan.Iteration.PhysicalPairs.SampledQuadrature
/-! The SAME unshifted colored carrier of the original graph42 has its literal
phase gradient in the existing source compact on the whole original chart.
This supplies the geometric input of the raw primary first mask, not its
amplitude estimates or a shifted-covector claim (main:eq:primary-strain). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPrimarySourcePhaseGeometryApplication
open Lean Meta Elab Command
private def ns := `JanetCartan.PhysicalPrimary.OriginalPrimarySourcePhaseGeometry
private def pairs := `JanetCartan.PhysicalInitialization.OriginalSampledPairs
private def col := `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def quad := `JanetCartan.PhysicalPairs.SampledQuadrature
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def bodyAt (e : Expr) : MetaM Expr := do
  let info ← getConstInfo e.getAppFn.constName!
  let some value := info.value? (allowOpaque := true) |
    throwError "primary source phase: missing original saved body"
  return ((value.instantiateLevelParams info.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta
private def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "primary source phase: unresolved native chart input"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let out ← liftM IO.getStdout
  liftM <| out.putStrLn s!"primary source phase: checking {key}/{p.size}"
  liftM <| out.flush
  addDecl (.thmDecl {name := ns ++ key,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore (ns ++ key) "The literal ordinary colored primary carrier on the SAME original graph42 source chart lies in the existing Ksource22. No shifted covector, doubled rate, new compact or analytic localization premise is used (main:eq:primary-strain; app:ch_regular:eq:source-tail)."
  logInfo m!"primary source phase: checked {key}/{p.size}"

elab "check_actual_primary_source_phase " which:num : command => liftTermElabM do
  let mode := which.getNat
  unless mode < 2 do throwError "primary source phase: unknown field"
  forallBoundedTelescope (← getConstInfo (pairs ++ `state)).type (some 44) fun p _ => do
    unless p.size == 44 do throwError "primary source phase: graph42+point/chart changed"
    let original := p[:42].toArray
    let static := p[:22].toArray
    let n := app ``Nat.succ #[p[0]!]
    let state := app (pairs ++ `state) p
    let familyEq := app (col ++ `family_eq_currentGroup) (static.push state)
    let equality ← inferType familyEq
    unless equality.isAppOfArity ``Eq 3 do throwError "primary source phase: original family/current equality changed"
    let current := equality.getAppArgs[2]!
    unless current.isAppOfArity `JanetCartan.ActualCarriers.ConstructedSignedGeometry.currentGroup 12 do
      throwError "primary source phase: lost literal currentGroup"
    let G := app (col ++ `Groups) static
    let S := app (col ++ `Scolor) static
    let K := app (col ++ `Ksource) static
    withLocalDeclD `g G fun g => do
      let subtype ← mkAppM ``Subtype #[mkApp S g]
      withLocalDeclD `z subtype fun z => do
        let all := p ++ #[g,z]
        let point := Expr.proj ``Subtype 0 z
        if mode == 0 then
          let hfamily := app `JanetCartan.PhysicalPrimary.OriginalPrimarySourceGeometry.colored_carrier_mem_source
            (static ++ #[state,Expr.proj ``Prod 0 g,Expr.proj ``Prod 1 g,z])
          let eg ← mkAppM ``congrFun #[familyEq,g]
          let ep ← mkAppM ``congrFun #[eg,point]
          let hcurrent ← mkAppM (quad ++ `gradient_source_mem)
            #[K,← mkAppM ``Eq.symm #[ep],hfamily]
          save `current_carrier_mem_source all hcurrent (← inferType hcurrent)
          return
        let hcurrent := app (ns ++ `current_carrier_mem_source) all
        let phase := app (quad ++ `group_phase) original
        let radial ← bodyAt phase
        unless radial.isAppOfArity (quad ++ `radialCarrier) 11 do
          throwError "primary source phase: original ordinary radial phase changed"
        let ca := radial.getAppArgs
        let reached ← inferType original[37]!
        let stage := reached.getAppArgs[2]!
        unless stage.isAppOfArity (reg ++ `Graph.S) 34 do
          throwError "primary source phase: original reached graph threshold changed"
        let fixed := stage.getAppArgs[:23].toArray
        let ordinary := #[n] ++ fixed[1:21].toArray
        let capped := app `JanetCartan.PhysicalNormalInverse.strongCappedExtra #[n,p[1]!,ordinary[20]!]
        let selected := ordinary.set! 20 capped
        let f := app (reg ++ `f) fixed
        let fa := (← inferType f).getAppArgs
        let args := #[p[0]!,p[1]!,app `JanetCartan.PhysicalInitialization.OriginalProtected.r ordinary,
          app `JanetCartan.PhysicalSeed.SelectedBoundary.rMeasure selected,
          app `JanetCartan.PhysicalInitialization.OriginalProtected.fact2 ordinary,
          app `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure selected,fa[fa.size-2]!,fa.back!,f,
          app (reg ++ `r) fixed]
        let inside := app (quad ++ `chart_in_carriers) (args ++ #[p[42]!,p[43]!])
        let hx := mkApp inside (mkApp ca[6]! g)
        let hD := app `JanetCartan.PhysicalSeed.OriginalBoundary.hD #[n,p[1]!]
        let ht := (← inferType hD).getAppArgs
        let gradArgs := #[n,ca[1]!,ht[ht.size-2]!,ht.back!,hD] ++ ca[2:11].toArray ++
          #[g,p[42]!,point,hx,Expr.proj ``Subtype 1 z]
        let gradName := `JanetCartan.SignedProductEstimates.currentGroup_eq_gradient_radial_carrier
        let gradInfo ← getConstInfo gradName
        let hgradient := mkAppN (mkConst gradName (gradInfo.levelParams.map fun _ => .zero)) gradArgs
        let result ← mkAppM (quad ++ `gradient_source_mem)
          #[K,← mkAppM ``Eq.symm #[hgradient],hcurrent]
        let literalGradient ← mkAppM ``gradient #[mkAppN phase #[g,point],p[42]!]
        let target ← mkAppM ``Membership.mem #[K,literalGradient]
        save `gradient_mem_source all result target
check_actual_primary_source_phase 0
check_actual_primary_source_phase 1
#print axioms JanetCartan.PhysicalPrimary.OriginalPrimarySourcePhaseGeometry.current_carrier_mem_source
#print axioms JanetCartan.PhysicalPrimary.OriginalPrimarySourcePhaseGeometry.gradient_mem_source
end JanetCartan.PhysicalPrimary.OriginalPrimarySourcePhaseGeometryApplication
end
