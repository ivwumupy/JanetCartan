module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Connect the original weak38 uncut solver to its physical equation without
reselecting an inverse, a cutoff, a source operator, or a current. The entire
native paired-source-minus-identity discrepancy stays in the conclusion. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalUncutEquationTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalUncutEquation
private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def current := regular ++ `Current
private def uncut := `JanetCartan.PhysicalPrimary.OriginalUncutSolver

private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | i+1 => part (.proj ``And 1 e) i

private def bodyAt (name : Name) (params : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo name).value? | throwError "uncut equation: no body for {name}"
  return value.beta params

private def retain (name : Name) (params : Array Expr) (value : Expr)
    (isDef := false) : MetaM Expr := do
  let full := ns ++ name
  let value ← store full params value isDef
  addDocStringCore full "Actual original38 uncut physical equation on the original chi2 core, retaining the SAME normalized paired source minus identity; no repeated chi2, inverse, output cutoff, or analytic premise (app:ch_regular:eq:exact-physical)."
  return value

private def closed (target : Expr) (name : Name) : MetaM Expr := do
  let result ← mkFreshExprMVar target
  let rest ← result.mvarId!.apply (← mkConstWithFreshMVarLevels name)
  unless rest.isEmpty do throwError "uncut equation: {name} left primitive inputs"
  instantiateMVars result

private def sourceBallSubset (U V : Expr) : MetaM Expr := do
  let result ← mkFreshExprMVar (← mkAppM `Set.Subset #[U,V])
  let rest ← result.mvarId!.apply (← mkConstWithFreshMVarLevels `Metric.ball_subset_ball)
  unless rest.length == 1 do throwError "uncut equation: expected one native radius inequality"
  let remaining ← rest[0]!.apply (← mkConstWithFreshMVarLevels `min_le_left)
  unless remaining.isEmpty do throwError "uncut equation: native source ball is not min(r,physicalRadius)"
  instantiateMVars result

/-- Extract only an explicitly retained Lp representative; no operator is
reconstructed from an arbitrary smooth representative or chosen anew. -/
private def rightLpOfAE (proof : Expr) : MetaM Expr := do
  let type ← inferType proof
  unless type.isAppOfArity `Filter.EventuallyEq 5 do
    throwError "uncut equation: expected native a.e. equality"
  let rhs := type.appArg!
  unless rhs.isAppOfArity `MeasureTheory.AEEqFun.cast 6 do
    throwError "uncut equation: expected native AEEqFun function coercion"
  let quotient := rhs.appArg!
  unless quotient.isAppOfArity `Subtype.val 3 &&
      quotient.getAppArgs[0]!.isAppOf `MeasureTheory.AEEqFun do
    throwError "uncut equation: expected native Lp subtype coercion"
  return quotient.appArg!

elab "derive_original_uncut_equation" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (current ++ `normalized_solver)).type (some 38) fun x _ => do
    unless x.size == 38 do throwError "uncut equation: expected exact weak original38"
    let fixed := x[:23].toArray
    let stat (name : Name) := mkAppN (mkConst (regular ++ name)) fixed
    let cur (name : Name) := mkAppN (mkConst (current ++ name)) x
    let rawR ← bodyAt (current ++ `R) x
    unless rawR.isAppOfArity `JanetCartan.ArbitraryAccuracy.ResidualLocalization.localRealCompression 6 do
      throwError "uncut equation: native localized real residual changed"
    let rargs := rawR.getAppArgs
    let hW := rargs[3]!
    let U := rargs[4]!
    let nativeResidual := rargs[5]!
    unless nativeResidual.isAppOf `JanetCartan.RegularSector.NormalizedSolver.pairedResidual do
      throwError "uncut equation: expected full native normalized paired residual"
    let pargs := nativeResidual.getAppArgs
    unless pargs.size >= 10 do throwError "uncut equation: incomplete native residual arguments"
    let a := pargs[pargs.size-10:].toArray
    -- Exact explicit suffix: f, compact, L, Q, B, output, ho, hob, W1, retarded1.
    let mask := stat `afterChoice_χ₃
    let hOpenU ← closed (← mkAppM `IsOpen #[U]) `Metric.isOpen_ball
    let hU ← mkAppM `IsOpen.measurableSet #[hOpenU]
    let hV := part mask 4
    let V := (← inferType hV).appArg!
    let hVU := part mask 5
    let hVW ← mkAppM `Set.Subset.trans #[hVU,stat `hUW]
    let hVm ← mkAppM `IsOpen.measurableSet #[hV]
    discard <| retain `core x V true
    discard <| retain `core_open x hV
    discard <| retain `core_subset_source x hVU
    discard <| retain `core_subset_domain x hVW
    let source ← retain `source x (← mkAppM (ns ++ `inverseSource) #[stat `χ₃,cur `Inv]) true
    let core ← mkAppM (ns ++ `uncutInverse_core_ae)
      #[hU,stat `χ₂,stat `χ₃,hVU,stat `hUW,part mask 2,
        cur `R,cur `Kloc,cur `Inv,cur `fact8,cur `fact11]
    let core ← retain `source_core_ae x core
    let wholeTest := part (part (part (cur `fact5) 0) 0) 2
    let partialTest ← mkAppM `JanetCartan.FixedDomainInverse.normalized_correctedSource_test
      #[a[0]!,a[1]!,a[2]!,a[3]!,a[4]!,a[8]!,a[5]!,a[6]!,a[7]!,cur `retarded,
        hW,hVm,hVU,hVW]
    let .forallE _ testType _ _ ← whnf (← inferType partialTest)
      | throwError "uncut equation: missing all-Lp native tested input"
    let smallTest ← forallTelescope testType fun args _ => do
      unless args.size == 6 do throwError "uncut equation: native test signature changed"
      let appliedNativeTest := mkAppN wholeTest args[:4].toArray
      let .forallE _ supportType _ _ ← whnf (← inferType appliedNativeTest)
        | throwError "uncut equation: native test missing support condition"
      let hUr ← sourceBallSubset U supportType.appArg!
      let support ← mkAppM `Set.Subset.trans #[args[4]!,hUr]
      mkLambdaFVars args (mkAppN appliedNativeTest #[support,args[5]!])
    let smallTest ← retain `native_tested x smallTest
    let partialTest := mkApp partialTest smallTest
    let partialRight ← mkAppM `JanetCartan.FixedDomainInverse.normalized_correctedSource_right_ae
      #[a[0]!,a[1]!,a[2]!,a[3]!,a[4]!,a[8]!,a[5]!,a[6]!,a[7]!,a[9]!,
        hW,hVm,hVU,hVW]
    let (right, tested) ← forallBoundedTelescope (← inferType core) (some 1) fun hs _ => do
      let h := hs[0]!
      let z := mkApp (← mkAppM `DFunLike.coe #[source]) h
      let hc := mkApp core h
      let right ← mkLambdaFVars hs (mkAppN partialRight #[h,z,hc])
      let tested ← mkLambdaFVars hs (mkAppN partialTest #[h,z,hc])
      pure (right,tested)
    let right ← retain `right_ae x right
    let tested ← retain `tested x tested
    let solverAE := mkAppN (mkConst (uncut ++ `uncut_solver_ae)) x
    let smooth := mkAppN (mkConst (uncut ++ `uncut_solver_smooth)) x
    let physical ← forallBoundedTelescope (← inferType solverAE) (some 1) fun hs _ => do
      let h := hs[0]!
      let hL2 ← mkAppM `Subtype.val #[h]
      let he := mkApp solverAE h
      let heType ← inferType he
      unless heType.isAppOfArity `Filter.EventuallyEq 5 do
        throwError "uncut equation: actual smooth solver a.e. signature changed"
      let v := heType.getAppArgs[3]!
      let u ← rightLpOfAE he
      let g ← rightLpOfAE (mkApp right hL2)
      let proof ← mkAppM (ns ++ `smooth_real_equation_ae)
        #[cur `Q,cur `B,cur `hQ,cur `hB,hV,v,mkApp smooth h,u,g,he,mkApp tested hL2]
      mkLambdaFVars hs proof
    discard <| retain `physical_ae x physical
    logInfo "actual weak38 uncut physical equation: all-Lp original core identity and globally smooth solver, SAME chi3*Inv, full paired-source minus identity retained"

end JanetCartan.PhysicalPrimary.OriginalUncutEquationTemplate
end
