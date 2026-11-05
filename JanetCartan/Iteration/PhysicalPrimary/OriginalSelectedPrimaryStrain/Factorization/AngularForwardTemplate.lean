module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularData
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
/-! Actual full-angular forward formula consumed by the original raw source
factorization (main:eq:primary-strain). The raw native formula exposes the
literal fullPrimaryWave body; the checked raw_angular name abbreviates exactly
that wave. The ordinary phase and original input remain unchanged. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
open Lean Meta Elab Command
namespace JanetCartan.PhysicalPrimary.OriginalRawAngularActualApplication
open OriginalRawPrimaryRealizationApplication
private def forwardLhs (lhs field : Expr) : MetaM Expr := do
  unless lhs.isAppOfArity ``HSMul.hSMul 6 do throwError "actual raw angular: observation changed"
  let a := lhs.getAppArgs
  let phase := a[5]!
  unless phase.isAppOfArity ``HSMul.hSMul 6 do throwError "actual raw angular: carrier demodulation changed"
  let b := phase.getAppArgs
  let matrix := b[5]!
  unless (matrix.find? (·.isAppOfArity
      `JanetCartan.RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix 2)).isSome do
    throwError "actual raw angular: original raw matrix conversion changed"
  let some derivative := matrix.find? (·.isAppOf ``fderiv) |
    throwError "actual raw angular: not the raw differential"
  let d := derivative.getAppArgs
  unless d[d.size-2]!.isAppOfArity
      `JanetCartan.RawPrimary.fullPrimaryWave 18 do
    throwError "actual raw angular: derivative is not the same complete raw angular field"
  let namedDerivative := mkAppN derivative.getAppFn (d.set! (d.size-2) field)
  let matrix := matrix.replace fun e => if e == derivative then some namedDerivative else none
  let phase := mkAppN phase.getAppFn (b.set! 5 matrix)
  return mkAppN lhs.getAppFn (a.set! 5 phase)
elab "check_actual_raw_angular_forward " mode:num : command => liftTermElabM do
  actualTelescope (← getConstInfo actualG).type fun p _ => do
    let original ← bodyAt (app actualG p)
    unless original.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.G 65 do
      throwError "actual raw angular: original native parameter spine changed"
    let parameter := original.getAppArgs
    let (n,N,J,φ,m,A) ← sumData p
    if mode.getNat == 1 || mode.getNat == 4 then
      let producer := app (native ++ `raw_full_forward_on_source) parameter
      forallBoundedTelescope (← inferType producer) (some 3) fun tail _ => do
        unless tail.size == 3 do throwError "actual raw angular: expected input/point/source membership"
        let w := tail[0]!
        let x := tail[1]!
        let proof := mkAppN producer tail
        let target ← inferType proof
        unless target.isAppOfArity ``Eq 3 do throwError "actual raw angular: raw equality changed"
        let lhs ← forwardLhs target.getAppArgs[1]! (app (actual ++ `raw_angular) (p.push (wideInput n J w)))
        let rhs := app ``forwardSum #[n,N,J,φ,m,A,w,x]
        let target ← mkEq lhs rhs
        let all := p ++ tail
        if mode.getNat == 1 then
          publish `unprefixed_forward_statement all target (mkSort .zero) true
        else
          publish `unprefixed_forward all proof (app (actual ++ `unprefixed_forward_statement) all)
    else if mode.getNat == 2 || mode.getNat == 5 then
      let base := app (actual ++ `unprefixed_forward) p
      withLocalDeclD `cut (mkConst ``Nat) fun cut => do
        forallBoundedTelescope (← inferType base) (some 3) fun tail _ => do
          let w := tail[0]!
          let x := tail[1]!
          let rw := app `JanetCartan.RawInputPartition.refinedPrefix #[n,J,cut,w]
          let initial := mkAppN base (tail.set! 0 rw)
          let hp := app ``forwardSum_prefix #[n,N,J,φ,m,A,cut,w,x]
          let initialType ← bodyAt
            (app (actual ++ `unprefixed_forward_statement) (p ++ tail.set! 0 rw))
          let hpType ← inferType hp
          unless initialType.isAppOfArity ``Eq 3 && hpType.isAppOfArity ``Eq 3 do
            throwError "actual raw angular: original prefix equality changed"
          let ia := initialType.getAppArgs
          let both := mkAppN (mkConst ``Eq.trans initialType.getAppFn.constLevels!)
            #[ia[0]!,ia[1]!,ia[2]!,hpType.getAppArgs[2]!,initial,hp]
          let oldwide := wideInput n J rw
          let goal ← inferType both
          let eq := goal.getAppArgs
          let hwide := app ``wide_prefix_eq #[n,J,cut,w]
          let hwideType ← inferType hwide
          let hwa := hwideType.getAppArgs
          let context ← withLocalDeclD `v (← inferType oldwide) fun v =>
            mkLambdaFVars #[v] (eq[1]!.replace fun e => if e == oldwide then some v else none)
          let transfer ← mkAppM ``congrArg #[context,hwide]
          let proof ← mkAppM ``Eq.trans #[transfer,both]
          unless (← inferType proof).getAppArgs[1]!.find? (· == hwa[1]!) |>.isSome do
            throwError "actual raw angular: original wide prefix was not retained"
          let all := p ++ #[cut] ++ tail
          if mode.getNat == 2 then
            publish `prefixed_forward_statement all (← inferType proof) (mkSort .zero) true
          else
            publish `prefixed_forward all proof (app (actual ++ `prefixed_forward_statement) all)
    else throwError "actual raw angular: unknown stage"
end JanetCartan.PhysicalPrimary.OriginalRawAngularActualApplication
end
