module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Native
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Components
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticCoordinates
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! Read the already checked native actual56 equality without repeatedly
substituting its complete parameter spine. Only syntax is shared; all new
equalities still pass the ordinary kernel check (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template

open Lean Meta Elab Command
open OriginalRawAngularActualApplication

/-- Preserve the stored actual binder types and substitute the remaining
expression once. -/
def withStoredTelescope (key : Name) (count : Nat)
    (go : Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  unless count == 53 || count == 55 || count == 56 do
    throwError "raw angular bridge: unexpected stored equality telescope"
  loop count (← getConstInfo key).type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0,type,p => go p (type.instantiateRev p)
    | k+1,type,p => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "raw angular bridge: stored equality ended at {p.size}"
      if bi == .instImplicit then
        withLocalDecl name bi (domain.instantiateRev p) fun x => loop k body (p.push x)
      else
        withLocalDeclNoLocalInstanceUpdate name bi (domain.instantiateRev p) fun x =>
          loop k body (p.push x)

def storedType (key : Name) (p : Array Expr) : MetaM Expr := do
  let mut type := (← getConstInfo key).type
  for _ in p do
    let .forallE _ _ body _ := type.consumeMData |
      throwError "raw angular bridge: stored component telescope changed"
    type := body
  return type.instantiateRev p

/-- Unfold exactly one of this bridge's already checked equality predicates,
without normalizing any phase, field, source or current. -/
def unfoldEquality (type : Expr) : MetaM Expr := do
  if type.isAppOfArity ``Eq 3 then return type
  unless type.getAppFn.constName?.any (root.isPrefixOf ·) do
    throwError "raw angular bridge: not a stored original equality predicate"
  let info ← getConstInfo type.getAppFn.constName!
  let result := (info.value! (allowOpaque := true)).beta type.getAppArgs
  unless result.isAppOfArity ``Eq 3 do
    throwError "raw angular bridge: stored predicate is not an exact equality"
  return result

def storedEquality (key : Name) (p : Array Expr) : MetaM Expr := do
  unfoldEquality (← storedType key p)

/-- Recover the same operands from the checked actual56 native proposition.
There is no application of the native68 theorem during this syntax read. -/
def withStoredParts (go : Parts → MetaM Unit) : MetaM Unit :=
  withStoredTelescope (root ++ `native_forward_statement) 56 fun all _ => do
    let p := all[:53].toArray
    let tail := all[53:56].toArray
    let info ← getConstInfo (root ++ `native_forward_statement)
    let type := (info.value! (allowOpaque := true)).beta all
    unless type.isAppOfArity ``Eq 3 do throwError "raw angular bridge: native equality changed"
    let lhs := type.getAppArgs[1]!
    let rhs := type.getAppArgs[2]!
    let some derivative := lhs.find? (·.isAppOf ``fderiv) |
      throwError "raw angular bridge: missing original derivative"
    let field := derivative.getAppArgs[derivative.getAppNumArgs-2]!
    let some phase := rhs.find? (·.isAppOfArity `JanetCartan.PhysicalForwardMean.singleRetainedForwardPhase 12) |
      throwError "raw angular bridge: missing original phase"
    let some product := rhs.find? fun e => e.isAppOfArity ``HMul.hMul 6 &&
        e.getAppArgs[5]!.isAppOfArity `JanetCartan.PhysicalForwardMean.singleBareScalarMask 4 |
      throwError "raw angular bridge: missing original single mask"
    let bare := product.getAppArgs[5]!.appFn!
    let angular := product.getAppArgs[4]!
    let mask ← forallBoundedTelescope (← inferType bare) (some 1) fun z _ =>
      mkLambdaFVars z (mkAppN product.appFn!.appFn! #[angular,mkAppN bare z])
    let some amplitude := rhs.find? (·.isAppOfArity
        `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.forwardSlice 7) |
      throwError "raw angular bridge: missing original raw slice"
    let namedPhase := app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.rawPhase p
    let phaseInfo ← getConstInfo namedPhase.getAppFn.constName!
    let rawPhase := ((phaseInfo.value! (allowOpaque := true)).beta p).headBeta
    unless rawPhase.isAppOfArity `JanetCartan.PhysicalForwardMean.singleRetainedForwardPhase 12 do
      throwError "raw angular bridge: named ordinary phase changed"
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let J := rawPhase.getAppArgs[1]!
    go {
      params := p, tail := tail, n := n,
      N := app `JanetCartan.embeddingDimension #[n], J := J,
      lhs := lhs, rhs := rhs, field := field, phase := phase, mask := mask,
      amplitude := amplitude,
      namedField := app (actual ++ `raw_angular) (p.push (wideInput n J tail[0]!)),
      namedPhase := namedPhase,
      namedMask := app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.rawMask p,
      namedAmplitude := app `JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.forwardAmplitude p }

elab "package_original_raw_angular_component " piece:num mode:num : command => liftTermElabM do
  let cases := #[`native_phase,`native_mask,`native_amplitude,`native_rhs]
  unless piece.getNat < cases.size && mode.getNat < 2 do
    throwError "raw angular bridge: unknown exact component package"
  let key := cases[piece.getNat]!
  if mode.getNat == 0 then
    withStoredParts fun c => do
      let (left,right,p) ← if piece.getNat == 0 then
          pure (c.phase,c.namedPhase,c.params)
        else if piece.getNat == 1 then pure (c.mask,c.namedMask,c.params)
        else if piece.getNat == 2 then pure (c.amplitude,c.namedAmplitude,c.params)
        else do
          let A ← liftAmplitude c.J c.amplitude
          let sum := app ``forwardSum #[c.n,c.N,c.J,c.phase,c.mask,A,c.tail[0]!,c.tail[1]!]
          pure (c.rhs,sum,c.params ++ c.tail[:2].toArray)
      save (key ++ `statement) p (← mkEq left right) (mkSort .zero) true
  else
    let count := if piece.getNat == 3 then 55 else 53
    let name := root ++ key ++ `statement
    withStoredTelescope name count fun p _ => do
      let info ← getConstInfo name
      let eq := (info.value! (allowOpaque := true)).beta p
      unless eq.isAppOfArity ``Eq 3 do throwError "raw angular bridge: component equality changed"
      let endpoint := if piece.getNat == 3 then `native_rhs_eq_sum
        else if piece.getNat == 0 then `native_phase_eq_actual
        else if piece.getNat == 1 then `native_mask_eq_actual
        else `native_amplitude_eq_actual
      save endpoint p (← mkEqRefl eq.getAppArgs[1]!) (app name p)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template
end
