module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Exact original23/current38 application of support from the literal
retarded/algebraic/elliptic output factors. No data or operator is reselected. -/

public meta section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Lean Meta Elab Command
namespace JanetCartan.PhysicalPrimary.OriginalSolverSupportTemplate
open JanetCartan.PhysicalInitialization.OriginalProtectedTemplate
private def root := `JanetCartan.PhysicalPrimary.OriginalSolverSupport
private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def current := regular ++ `Current

private def retain (name : Name) (params : Array Expr) (value : Expr)
    (isDef := false) (target : Option Expr := none) : MetaM Expr := do
  let result ← store name params value isDef target
  addDocStringCore name "The SAME original23 compact output and literal original38 solver; no new output cutoff, source restriction, or analytic support premise (app:ch_regular_base:eq:energy-complete-residual; main:prop:current-waves)."
  return result

private def part (h : Expr) (i : Nat) : MetaM Expr := do
  let mut h := h
  for _ in [:i] do
    let t ← whnf (← inferType h)
    unless t.isAppOfArity ``And 2 do throwError "missing conjunction branch {i}"
    h := mkAppN (mkConst ``And.right) (t.getAppArgs.push h)
  let t ← whnf (← inferType h)
  if t.isAppOfArity ``And 2 then return mkAppN (mkConst ``And.left) (t.getAppArgs.push h)
  return h
private def body (value : Expr) : MetaM Expr := do
  let some v := (← getConstInfo value.getAppFn.constName!).value? (allowOpaque := true)
    | throwError "missing native operator body {value.getAppFn}"
  return v.beta value.getAppArgs
private def foldOutput (type output K : Expr) : Expr :=
  type.replace fun e =>
    if e.isAppOfArity `tsupport 5 && e.getAppArgs.back! == output then some K else none
private def replaceOp (type fromOp toOp : Expr) : Expr :=
  type.replace fun e => if e == fromOp then some toOp else none

elab "construct_original_solver_support" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (regular ++ `output)).type (some 23) fun fixed _ => do
    unless fixed.size == 23 do throwError "expected exact static original23"
    let stat (key : Name) := mkAppN (mkConst (regular ++ key)) fixed
    let output := stat `output
    let supportSet ← mkAppM `tsupport #[output]
    let K ← retain (root ++ `outputSupport) fixed supportSet true
    let facts := stat `afterChoice_r
    let compact ← part facts 3
    discard <| retain (root ++ `outputSupport_compact) fixed compact false
      (some (← mkAppM `IsCompact #[K]))
    let hsupport ← part facts 4
    discard <| retain (root ++ `outputSupport_in_physical_ball) fixed hsupport false
      (some (foldOutput (← inferType hsupport) output K))
    let geometry ← mkAppM (root ++ `output_support_geometry) #[stat `f,hsupport]
    discard <| retain (root ++ `outputSupport_in_geometry) fixed geometry false
      (some (foldOutput (← inferType geometry) output K))
    let wide ← mkAppM (root ++ `output_support_wide) #[fixed[1]!,stat `f,hsupport]
    discard <| retain (root ++ `outputSupport_in_wide_geometry) fixed wide false
      (some (foldOutput (← inferType wide) output K))
    let plateau ← part facts 5
    let source := stat `afterChoice_χ₃
    for (key,i) in [(`χ₂_support_output,0),(`χ₃_support_output,1)] do
      let h ← mkAppM (root ++ `source_support_original_output) #[plateau,← part source i]
      discard <| retain (root ++ key) fixed h false (some (foldOutput (← inferType h) output K))
    logInfo "static original23: EXACT outputSupport compact, physical/coefficient/wide geometry, BOTH original source bumps inside; no new mask"
  forallBoundedTelescope (← getConstInfo (current ++ `normalized_solver)).type (some 38) fun params _ => do
    unless params.size == 38 do throwError "expected exact native original38"
    let fixed := params[:23].toArray
    let stat (key : Name) := mkAppN (mkConst (regular ++ key)) fixed
    let cur (key : Name) := mkAppN (mkConst (current ++ key)) params
    let K := mkAppN (mkConst (root ++ `outputSupport)) fixed
    let output := stat `output
    let zero ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 2)) 0
    let nativeHalf := mkApp (cur `Tplus) zero
    let nativeRetarded := mkApp (cur `retarded) zero
    let retarded := (mkApp (← body (cur `retarded)) zero).headBeta
    unless retarded.isAppOf `ContinuousLinearMap.comp do throwError "native retarded has no original left multiplier"
    let ra := retarded.getAppArgs
    let mout := ra[ra.size-2]!
    unless mout.isAppOf `JanetCartan.FourierIntegral.LowBounds.sourceCutMultiplier do
      throwError "native retarded lost its original sourceCutMultiplier"
    let R := ra.back!
    let factType ← inferType (cur `fact5)
    let some nativePaired := factType.find? (fun e =>
        e.isAppOf `JanetCartan.RegularSector.NormalizedSolver.pairedSolver)
      | throwError "missing literal native pairedSolver"
    let pa := nativePaired.getAppArgs
    unless pa.size == 16 do throwError "changed pairedSolver16 signature"
    unless ← isDefEq pa[12]! output do throwError "native paired output changed"
    unless ← isDefEq pa[15]! nativeRetarded do throwError "native paired retarded changed"
    let pairBody ← body nativePaired
    unless pairBody.isAppOf `JanetCartan.RegularSector.NormalizedSolver.normalizedPair do
      throwError "pairedSolver is not original normalizedPair"
    let rawSum := pairBody.getAppArgs.back!
    unless rawSum.isAppOf ``HAdd.hAdd do throwError "pairedSolver lost direct+elliptic sum"
    let sa := rawSum.getAppArgs
    let direct := sa[sa.size-2]!
    let ellComp := sa.back!
    unless direct.isAppOf `JanetCartan.RegularSector.FiniteAssembly.selectedFiniteDirectSolver do
      throwError "native direct solver was replaced"
    unless ellComp.isAppOf `ContinuousLinearMap.comp do throwError "elliptic output multiplier missing"
    let ea := ellComp.getAppArgs
    unless ← isDefEq ea[ea.size-2]! mout do throwError "elliptic branch uses another output"
    let El := ea.back!
    let directBody ← body direct
    unless directBody.isAppOf ``HAdd.hAdd do throwError "direct solver lost retarded/algebraic sum"
    let scalarTerm := directBody.getAppArgs.back!
    unless scalarTerm.isAppOf ``HSMul.hSMul do throwError "algebraic imaginary coefficient missing"
    let algebraicComp := scalarTerm.getAppArgs.back!
    unless algebraicComp.isAppOf `ContinuousLinearMap.comp do throwError "algebraic original output missing"
    let aa := algebraicComp.getAppArgs
    unless ← isDefEq aa[aa.size-2]! mout do throwError "algebraic branch uses another output"
    let A := aa.back!
    let result ← mkAppM (root ++ `factored_solver_outputs) #[output,pa[13]!,pa[14]!,R,A,El]
    let resultType ← inferType result
    let .letE _ _ actualMout rest _ := resultType | throwError "missing literal Mout let"
    let .letE _ _ half rest _ := rest.instantiate1 actualMout | throwError "missing literal half let"
    let .letE _ _ paired _ _ := rest.instantiate1 half | throwError "missing literal paired let"
    unless ← isDefEq actualMout mout do throwError "generic support proof changed original output"
    let pairedHalf := replaceOp paired half nativeHalf
    let halfEq ← mkEqRefl nativeHalf
    discard <| retain (root ++ `half_solver_factorization) params halfEq false
      (some (← mkEq nativeHalf half))
    discard <| retain (root ++ `retarded_factorization) params (← mkEqRefl nativeRetarded) false
      (some (← mkEq nativeRetarded retarded))
    discard <| retain (root ++ `paired_half_eq_native) params (← mkEqRefl nativePaired) false
      (some (← mkEq pairedHalf nativePaired))
    for (key,k,oldOp,newOp) in [
        (`half_solver_zero_off_output,0,half,nativeHalf),
        (`paired_half_zero_off_output,1,paired,pairedHalf),
        (`paired_solver_zero_off_output,1,paired,nativePaired),
        (`real_half_solver_zero_off_output,2,paired,pairedHalf),
        (`real_solver_zero_off_output,2,paired,nativePaired)] do
      let h ← part result k
      let target := foldOutput (replaceOp (← inferType h) oldOp newOp) output K
      discard <| retain (root ++ key) params h false (some target)
    logInfo "actual native38: original retarded factor, literal HALF Tplus0/full physical pair/native pairedSolver and real compression; ALL L2 inputs, EXACT original compact output"
end JanetCartan.PhysicalPrimary.OriginalSolverSupportTemplate
end
