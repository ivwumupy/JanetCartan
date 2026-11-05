module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.PhaseStatement
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Mask
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.AmplitudeStatement
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.SumBase
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.SumStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticCoordinates
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! Transport the SAME full annular sum under the two exact phase/amplitude
equality predicates, while their concrete proofs are checked independently.
`Sum.lean` discharges both predicates with the original actual identities;
the mask and native-sum equalities are already proved here. This logical
implication adds no analytic estimate (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template

open Lean Meta Elab Command
open OriginalRawAngularActualApplication

private def equalityType (h : Expr) : MetaM Expr := do
  if h.getAppFn.constName?.any (root.isPrefixOf ·) then
    storedEquality h.getAppFn.constName! h.getAppArgs
  else unfoldEquality (← inferType h)

/-- Construct transitivity with the exact middle expression already retained
by the original component equalities. No large unification step is needed. -/
def exactTrans (h₁ h₂ : Expr) : MetaM Expr := do
  let t₁ ← equalityType h₁
  let t₂ ← equalityType h₂
  unless t₁.isAppOfArity ``Eq 3 && t₂.isAppOfArity ``Eq 3 do
    throwError "raw angular bridge: a component transport lost its equality"
  let a := t₁.getAppArgs
  return mkAppN (mkConst ``Eq.trans t₁.getAppFn.constLevels!)
    #[a[0]!,a[1]!,a[2]!,t₂.getAppArgs[2]!,h₁,h₂]

/-- Lift a proved original-field equality through its literal context. -/
def exactCongr (f h : Expr) : MetaM Expr := do
  let t ← equalityType h
  unless t.isAppOfArity ``Eq 3 do
    throwError "raw angular bridge: missing original field equality"
  let a := t.getAppArgs
  let output ← inferType (f.beta #[a[1]!])
  return mkAppN (mkConst ``congrArg [.one,.one])
    #[a[0]!,output,a[1]!,a[2]!,f,h]

elab "transport_original_raw_angular_sum_from_components" : command => liftTermElabM do
  withStoredTelescope (root ++ `native_rhs_eq_sum) 55 fun p nativeEq => do
    let nativeEq ← unfoldEquality nativeEq
    unless nativeEq.isAppOfArity ``Eq 3 do
      throwError "raw angular bridge: missing native sum equality"
    let sum := nativeEq.getAppArgs[2]!
    unless sum.isAppOfArity ``forwardSum 8 do
      throwError "raw angular bridge: original full forward sum changed"
    let sa := sum.getAppArgs
    let actualParams := p[:53].toArray
    let φeq ← unfoldEquality (app (root ++ `native_phase.statement) actualParams)
    let meq ← storedEquality (root ++ `native_mask_eq_actual) actualParams
    let aeq ← unfoldEquality (app (root ++ `native_amplitude.statement) actualParams)
    let phase := φeq.getAppArgs[1]!
    let namedPhase := φeq.getAppArgs[2]!
    let mask := meq.getAppArgs[1]!
    let namedMask := meq.getAppArgs[2]!
    let amplitude := aeq.getAppArgs[1]!
    withLocalDeclD `hPhase (app (root ++ `native_phase.statement) actualParams) fun hPhase => do
      withLocalDeclD `hAmplitude (app (root ++ `native_amplitude.statement) actualParams) fun hAmplitude => do
        let J := sa[2]!
        let makeSum (φ m A : Expr) := mkAppN sum.getAppFn
          (sa.set! 3 φ |>.set! 4 m |>.set! 5 A)
        let A ← liftAmplitude J amplitude
        let phaseContext ← withLocalDeclD `phase (← inferType phase) fun φ =>
          mkLambdaFVars #[φ] (makeSum φ mask A)
        let hφ ← exactCongr phaseContext hPhase
        let maskContext ← withLocalDeclD `mask (← inferType mask) fun m =>
          mkLambdaFVars #[m] (makeSum namedPhase m A)
        let hm ← exactCongr maskContext (app (root ++ `native_mask_eq_actual) actualParams)
        let amplitudeContext ← withLocalDeclD `amplitude (← inferType amplitude) fun a => do
          mkLambdaFVars #[a] (makeSum namedPhase namedMask (← liftAmplitude J a))
        let ha ← exactCongr amplitudeContext hAmplitude
        let base := app (root ++ `native_rhs_eq_sum) p
        let proof ← exactTrans base (← exactTrans hφ (← exactTrans hm ha))
        let target := app (root ++ `actual_sum_statement) p
        save `native_rhs_of_phase_amplitude (p ++ #[hPhase,hAmplitude]) proof target

transport_original_raw_angular_sum_from_components

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template
end
