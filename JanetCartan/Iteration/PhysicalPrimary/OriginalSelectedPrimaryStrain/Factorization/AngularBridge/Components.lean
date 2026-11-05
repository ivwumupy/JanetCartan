module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticCoordinates
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! Exact field, phase, mask and amplitude components of the original raw
angular sum. Separating their equalities preserves the default kernel budget
for the primary source factorization (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template

open Lean Meta Elab Command
open OriginalRawAngularActualApplication

structure Parts where
  params : Array Expr
  tail : Array Expr
  n : Expr
  N : Expr
  J : Expr
  lhs : Expr
  rhs : Expr
  field : Expr
  phase : Expr
  mask : Expr
  amplitude : Expr
  namedField : Expr
  namedPhase : Expr
  namedMask : Expr
  namedAmplitude : Expr

def withParts (go : Parts → MetaM Unit) : MetaM Unit :=
  withNode fun p _ tail proof => do
    let type ← inferType proof
    unless type.isAppOfArity ``Eq 3 do
      throwError "raw angular bridge: the native derivative is not an equality"
    let lhs := type.getAppArgs[1]!
    let rhs := type.getAppArgs[2]!
    let some derivative := lhs.find? (·.isAppOf ``fderiv) |
      throwError "raw angular bridge: missing the native derivative"
    let field := derivative.getAppArgs[derivative.getAppNumArgs-2]!
    unless field.isAppOfArity `JanetCartan.RawPrimary.fullPrimaryWave 18 do
      throwError "raw angular bridge: the derivative lost the original full raw field"
    let some phase := rhs.find? (·.isAppOfArity `JanetCartan.PhysicalForwardMean.singleRetainedForwardPhase 12) |
      throwError "raw angular bridge: missing the original retained phase"
    let some product := rhs.find? fun e => e.isAppOfArity ``HMul.hMul 6 &&
        e.getAppArgs[5]!.isAppOfArity `JanetCartan.PhysicalForwardMean.singleBareScalarMask 4 |
      throwError "raw angular bridge: missing the single original scalar mask"
    let bare := product.getAppArgs[5]!.appFn!
    let angular := product.getAppArgs[4]!
    let mask ← forallBoundedTelescope (← inferType bare) (some 1) fun z _ => do
      mkLambdaFVars z (mkAppN product.appFn!.appFn! #[angular,mkAppN bare z])
    let some amplitude := rhs.find? (·.isAppOfArity
        `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.forwardSlice 7) |
      throwError "raw angular bridge: missing the original raw forward slice"
    for value in #[field,phase,mask,amplitude] do
      if value.hasLooseBVars then
        throwError "raw angular bridge: a native field escaped an integral variable"
    let (n,N,J,namedPhase,namedMask,_) ← sumData p
    go {
      params := p
      tail := tail
      n := n
      N := N
      J := J
      lhs := lhs
      rhs := rhs
      field := field
      phase := phase
      mask := mask
      amplitude := amplitude
      namedField := app (actual ++ `raw_angular) (p.push (wideInput n J tail[0]!))
      namedPhase := namedPhase
      namedMask := namedMask
      namedAmplitude := app `JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.forwardAmplitude p }

/-- Repeat only the SAME two-coordinate amplitude across the original annular
labels; the input partition and its number of labels are unchanged. -/
def liftAmplitude (J amplitude : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType amplitude) (some 2) fun ac _ =>
    withLocalDeclD `j (app `JanetCartan.RawInputPartition.RefinedIndex #[J]) fun j =>
      mkLambdaFVars (ac.push j) (mkAppN amplitude ac)

elab "identify_original_raw_angular_component " mode:num : command => liftTermElabM do
  withParts fun c => do
    if mode.getNat == 0 then
      save `raw_field_eq_native (c.params.push c.tail[0]!)
        (← mkEqRefl c.namedField) (← mkEq c.namedField c.field)
    else if mode.getNat == 1 then
      save `native_phase_eq_actual c.params
        (← mkEqRefl c.phase) (← mkEq c.phase c.namedPhase)
    else if mode.getNat == 2 then
      save `native_mask_eq_actual c.params
        (← mkEqRefl c.mask) (← mkEq c.mask c.namedMask)
    else if mode.getNat == 3 then
      save `native_amplitude_eq_actual c.params
        (← mkEqRefl c.amplitude) (← mkEq c.amplitude c.namedAmplitude)
    else if mode.getNat == 4 then
      let A ← liftAmplitude c.J c.amplitude
      let rhs := app ``forwardSum #[c.n,c.N,c.J,c.phase,c.mask,A,c.tail[0]!,c.tail[1]!]
      save `native_rhs_eq_sum (c.params ++ c.tail[:2].toArray)
        (← mkEqRefl c.rhs) (← mkEq c.rhs rhs)
    else throwError "raw angular bridge: unknown original component"

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template
end
