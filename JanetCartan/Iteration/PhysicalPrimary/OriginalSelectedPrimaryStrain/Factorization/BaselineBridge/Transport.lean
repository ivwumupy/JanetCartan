module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineData
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge.Template
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# Transport the native baseline equality through its exact component names

Only congruence, symmetry and transitivity are used after the native theorem
and the two function equalities have been checked. The target is the unchanged
`Actual.baseline_factor_statement/59`, including the original outer-weight
admission and source-chart membership (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge.Template

open Lean Meta

private def closeFactor : MetaM Unit :=
  withStoredTelescope (actual ++ `baseline_factor_statement) 59 fun all _ => do
    let c ← parts all (← bodyAt (app (root ++ `native_factor_statement) all))
    let p := all[:56].toArray
    let target ← bodyAt (app (actual ++ `baseline_factor_statement) all)
    unless target.isAppOfArity ``Eq 3 do
      throwError "raw baseline bridge: final named equality changed"
    let eq := c.equation.getAppArgs
    let matrixType := eq[0]!
    let nativeLeft := eq[1]!
    let nativeRight := eq[2]!
    let fieldEq ← bodyAt (app (root ++ `wave_statement) p)
    let amplitudeEq ← bodyAt (app (root ++ `amplitude_statement) p)
    unless fieldEq.isAppOfArity ``Eq 3 && amplitudeEq.isAppOfArity ``Eq 3 do
      throwError "raw baseline bridge: component equality changed"
    let f := fieldEq.getAppArgs
    let a := amplitudeEq.getAppArgs
    let fieldContext ← withLocalDeclD `baselineField f[0]! fun v =>
      mkLambdaFVars #[v] (nativeLeft.replace fun e => if e == c.field then some v else none)
    let namedLeft := (fieldContext.beta #[f[1]!]).headBeta
    let left := mkAppN (mkConst ``congrArg [.one, .one])
      #[f[0]!, matrixType, f[1]!, f[2]!, fieldContext, app (root ++ `wave_eq_native) p]
    let amplitudeContext ← withLocalDeclD `baselineAmplitude a[0]! fun v => do
      let rhs := mkAppN nativeRight.getAppFn (nativeRight.getAppArgs.set! 5 (mkApp v all[57]!))
      mkLambdaFVars #[v] rhs
    let namedRight := (amplitudeContext.beta #[a[1]!]).headBeta
    let rightForward := mkAppN (mkConst ``congrArg [.one, .one])
      #[a[0]!, matrixType, a[1]!, a[2]!, amplitudeContext, app (root ++ `amplitude_eq_native) p]
    let right := mkAppN (mkConst ``Eq.symm c.equation.getAppFn.constLevels!)
      #[matrixType, namedRight, nativeRight, rightForward]
    let trans := mkConst ``Eq.trans c.equation.getAppFn.constLevels!
    let tail := mkAppN trans
      #[matrixType, nativeLeft, nativeRight, namedRight, app (root ++ `native_factor) all, right]
    let proof := mkAppN trans #[matrixType, namedLeft, nativeLeft, namedRight, left, tail]
    save (actual ++ `baseline_factor) all proof (app (actual ++ `baseline_factor_statement) all)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge.Template
end
