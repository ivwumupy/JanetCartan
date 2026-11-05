module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticCoordinates
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWavesTemplate
/-! BEFORE-B raw angular realization in the SAME original forward coordinates.
Only the original geometric arguments of the generic-in-A annular coordinate
identity are reused. The derivative identity is the independently proved RAW
matrix integral. The zero angular branch is retained without division, and
no periodic corrected G is relabeled (main:eq:primary-strain). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalPrimary.OriginalRawPrimaryForwardRealizationApplication
open Lean Meta Elab Command
open OriginalRawPrimaryRealizationApplication
private def root := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Native
private def waves := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def model := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.retained_coordinates_on_original_annuli
private def functionScalarParts (rhs : Expr) : MetaM (Expr × Expr) := do
  if rhs.isAppOfArity ``HSMul.hSMul 6 then
    return (rhs.getAppArgs[4]!,rhs.getAppArgs[5]!)
  lambdaTelescope rhs fun point body => do
    unless point.size == 1 && body.isAppOfArity ``HSMul.hSMul 6 do
      throwError "raw angular realization: original pointwise raw scalar factor changed"
    return (body.getAppArgs[4]!,← mkLambdaFVars point body.getAppArgs[5]!)
private def transEq (first second : Expr) : MetaM Expr := do
  let ft ← inferType first
  let st ← inferType second
  unless ft.isAppOfArity ``Eq 3 && st.isAppOfArity ``Eq 3 do
    throwError "raw forward realization: actual equalities changed"
  let a := ft.getAppArgs
  let b := st.getAppArgs
  return mkAppN (mkConst ``Eq.trans ft.getAppFn.constLevels!) #[a[0]!,a[1]!,a[2]!,b[2]!,first,second]

elab "check_raw_native_forward_coordinates" : command => liftTermElabM do
  let original := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.native_forward_realization
  forallBoundedTelescope (← getConstInfo original).type (some 67) fun all _ => do
    unless all.size == 67 do throwError "raw forward coordinates: original67 changed"
    let old ← bodyAt (app original all)
    unless old.isAppOfArity ``Eq.trans 6 do
      throwError "raw forward coordinates: expected original generic coordinate step"
    let geometry := old.getAppArgs[5]!
    unless geometry.isAppOf model do
      throwError "raw forward coordinates: original geometry was not generic in the matrix amplitude"
    let known ← arguments geometry
    let A ← get known `A
    unless A.isAppOfArity `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude 16 do
      throwError "raw forward coordinates: original matrix parameter changed"
    let a := A.getAppArgs
    let raw := app `JanetCartan.RawPrimary.fullDerivativeAmplitude (a[:12].toArray ++ #[a[14]!,a[15]!])
    let n := mkApp (mkConst ``Nat.succ) all[0]!
    withLocalDeclNoLocalInstanceUpdate `x .default (app `JanetCartan.Euclidean #[n]) fun x => do
      let proof ← applyNamed model (#[(`A,raw),(`x,x)] ++ known)
      save `raw_coordinates (all[:66].toArray.push x) proof

elab "check_raw_full_forward_on_source" : command => liftTermElabM do
  let source := root ++ `raw_coordinates
  forallBoundedTelescope (← getConstInfo source).type (some 67) fun all _ => do
    unless all.size == 67 do throwError "raw angular realization: native67 changed"
    let coordinates := app source all
    let geometric := (← bodyAt coordinates)
    unless geometric.isAppOf model do
      throwError "raw angular realization: lost the independently instantiated raw coordinates"
    let known ← arguments geometric
    let params := all[:65].toArray
    let w := all[65]!
    let x := all[66]!
    let n := mkApp (mkConst ``Nat.succ) all[0]!
    let N ← get known `N
    let J ← get known `J
    let T ← get known `T
    unless T.isAppOfArity (waves ++ `T) 53 do
      throwError "raw angular realization: same source53 family changed"
    let chart := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart T.getAppArgs[:23].toArray
    let wide ← bodyAt (app ``PhysicalMean.OriginalMeanQuadraticProfilesTemplate.original_refined_input #[n,J,w])
    let ψx := mkApp (← get known `ψ) x
    let support := mkApp (app (waves ++ `Whole.inner_factor_support) params[:61].toArray) params[64]!
    let .forallE _ nonzero _ _ ← inferType support |
      throwError "raw angular realization: original active-inner admission changed"
    withLocalDeclNoLocalInstanceUpdate `hx .default (← mkAppM ``Membership.mem #[chart,x]) fun hx => do
      let (phase,result,hactive) ← withLocalDeclNoLocalInstanceUpdate `ha .default nonzero fun ha => do
        let admitted := mkApp support ha
        let membership ← inferType admitted
        unless membership.isAppOfArity ``Membership.mem 5 do
          throwError "raw angular realization: original carrier admission lost membership"
        let carrier := membership.getAppArgs[4]!
        let bareParams := params[:64].toArray ++ #[carrier,admitted]
        let smooth := app (waves ++ `Whole.raw_on_source_chart) (bareParams.push wide)
        let restricted ← bodyAt smooth
        unless restricted.isAppOfArity ``ContDiffOn.mono 14 do
          throwError "raw angular realization: original source-to-cell restriction changed"
        let hxCell := mkAppN restricted.getAppArgs[13]! #[x,hx]
        let integral := app (root ++ `raw_matrix_annuli) (bareParams ++ #[w,x,hxCell])
        let equation ← inferType integral
        unless equation.isAppOfArity ``Eq 3 do
          throwError "raw angular realization: genuine RAW annular identity changed"
        let e := equation.getAppArgs
        unless e[1]!.isAppOfArity ``HSMul.hSMul 6 do
          throwError "raw angular realization: exact raw demodulation changed"
        let phase := e[1]!.getAppArgs[4]!
        let observation ← withLocalDeclNoLocalInstanceUpdate `M .default e[0]! fun M => do
          mkLambdaFVars #[M] (← mkAppM ``HSMul.hSMul #[ψx,M])
        let proof := mkAppN (mkConst ``congrArg [.one,.one])
          #[e[0]!,e[0]!,e[1]!,e[2]!,observation,integral]
        let result := (observation.beta #[e[2]!]).headBeta
        if phase.hasLooseBVars || result.hasLooseBVars then
          throwError "raw angular realization: coordinate data escaped its original node"
        return (phase,result,← mkLambdaFVars #[ha] proof)
      let fieldFactor := app (waves ++ `Whole.full_angular_factor.raw) (params.push wide)
      let factor ← inferType fieldFactor
      unless factor.isAppOfArity ``Eq 3 do
        throwError "raw angular realization: original full raw factor changed"
      let f := factor.getAppArgs
      let (a,bare) ← functionScalarParts f[2]!
      let differential ← applyNamed ``PhysicalMean.OriginalCanonicalDerivativeTemplate.whole_derivative_factor
        #[(`n,n),(`N,N),(`a,a),(`full,f[1]!),(`bare,bare),(`hfield,fieldFactor),(`phase,phase),(`x,x)]
      let dt ← inferType differential
      let da := dt.getAppArgs
      unless dt.isAppOfArity ``Eq 3 && da[2]!.isAppOfArity ``HSMul.hSMul 6 do
        throwError "raw angular realization: zero-safe RAW derivative scaling changed"
      let restored ← applyNamed ``PhysicalMean.OriginalMeanQuadraticProfilesTemplate.original_restore_angular_observation
        #[(`n,n),(`N,N),(`a,da[2]!.getAppArgs[4]!),(`ψ,ψx),(`full,da[1]!),
          (`bare,da[2]!.getAppArgs[5]!),(`result,result),(`hfull,differential),(`hactive,hactive)]
      save `raw_full_forward_on_source (all.push hx) (← transEq restored coordinates)
check_raw_native_forward_coordinates
check_raw_full_forward_on_source
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Native.raw_coordinates
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Native.raw_full_forward_on_source
end JanetCartan.PhysicalPrimary.OriginalRawPrimaryForwardRealizationApplication
end
