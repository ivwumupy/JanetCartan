module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineData
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# The original retained-background differential before naming its fields

The consumer is `OriginalRawPrimaryRealization.Actual.baseline_factor`, the
baseline input to the same-source primary differential factorization in
`main:eq:primary-strain`. Only the existing outer-node regularity operands are
read from `native_demodulation`; the mathematical producer is the raw theorem
`RetainedBackground.background_differential_eq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge.Template

open Lean Meta

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge
private def actual := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Actual
private def baseline := `JanetCartan.PhysicalPrimary.OriginalRawBaselineProfiles
private def old := `JanetCartan.PhysicalPairs.OriginalBaselineNode
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p

private def bodyAt (e : Expr) : MetaM Expr := do
  let ci ← getConstInfo e.getAppFn.constName!
  let some value := ci.value? (allowOpaque := true) |
    throwError "raw baseline bridge: unavailable original body {ci.name}"
  return ((value.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta

/-- Substitute the original arguments once, preserving every stored binder. -/
private def typeAt (e : Expr) : MetaM Expr := do
  let ci ← getConstInfo e.getAppFn.constName!
  let mut type := ci.type.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!
  for _ in e.getAppArgs do
    let .forallE _ _ rest _ := type.consumeMData |
      throwError "raw baseline bridge: changed original telescope {ci.name}"
    type := rest
  return type.instantiateRev e.getAppArgs

private def withStoredTelescope (key : Name) (count : Nat)
    (next : Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  unless count == 56 || count == 57 || count == 59 do
    throwError "raw baseline bridge: unexpected original parameter count"
  loop count (← getConstInfo key).type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0, type, p => next p (type.instantiateRev p)
    | k+1, type, p => do
      let .forallE key domain rest bi := type.consumeMData |
        throwError "raw baseline bridge: stored telescope ended at {p.size}"
      if bi == .instImplicit then
        withLocalDecl key bi (domain.instantiateRev p) fun x => loop k rest (p.push x)
      else
        withLocalDeclNoLocalInstanceUpdate key bi (domain.instantiateRev p) fun x =>
          loop k rest (p.push x)

/-- The exact old outer57 regularity spine, followed by its original x/hx.
No corrected differential theorem is used as a mathematical premise. -/
private def withNative
    (next : Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  withStoredTelescope (old ++ `native_demodulation_statement) 57 fun p _ => do
    forallBoundedTelescope (← bodyAt (app (old ++ `native_demodulation_statement) p))
        (some 2) fun xy _ => do
      unless xy.size == 2 do throwError "raw baseline bridge: original point/source tail changed"
      let metadata ← bodyAt (app (old ++ `native_demodulation) (p ++ xy))
      unless metadata.isAppOf `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude_eq_demodulated do
        throwError "raw baseline bridge: original retained regularity spine changed"
      let known ← OriginalRawPrimaryRealizationApplication.arguments metadata
      let w ← OriginalRawPrimaryRealizationApplication.get known `w
      unless w.isAppOfArity ``Prod.mk 4 do
        throwError "raw baseline bridge: original outer point changed"
      let z ← mkAppM ``Prod.fst #[w.getAppArgs[3]!]
      let proof ← OriginalRawPrimaryRealizationApplication.applyNamed
        ``Sampling.RetainedBackground.background_differential_eq
        (#[(`x, xy[0]!), (`z, z)] ++ known)
      let type ← typeAt proof
      unless type.isAppOfArity ``Eq 3 do
        throwError "raw baseline bridge: retained raw derivative is not an equality"
      next (p ++ xy) proof type

private structure Parts where
  params : Array Expr
  equation : Expr
  derivative : Expr
  field : Expr
  amplitude : Expr

/-- Read the literal components from the checked native equality. -/
private def parts (p : Array Expr) (equation : Expr) : MetaM Parts := do
  unless p.size == 59 && equation.isAppOfArity ``Eq 3 do
    throwError "raw baseline bridge: original native equality changed"
  let lhs := equation.getAppArgs[1]!
  let rhs := equation.getAppArgs[2]!
  let some derivative := lhs.find? (·.isAppOf ``fderiv) |
    throwError "raw baseline bridge: missing original derivative"
  let da := derivative.getAppArgs
  let field := da[da.size-2]!
  unless (field.find? (·.isAppOf `JanetCartan.RawPrimary.fullPrimaryAtom)).isSome do
    throwError "raw baseline bridge: native field is not the original fullPrimaryAtom"
  unless rhs.isAppOfArity ``HSMul.hSMul 6 &&
      rhs.getAppArgs[5]!.isAppOfArity `JanetCartan.RawPrimary.fullDerivativeAmplitude 15 do
    throwError "raw baseline bridge: native carrier or raw amplitude changed"
  return {
    params := p
    equation := equation
    derivative := derivative
    field := field
    amplitude := rhs.getAppArgs[5]! }

private def withStoredParts (next : Parts → MetaM Unit) : MetaM Unit :=
  withStoredTelescope (root ++ `native_factor_statement) 59 fun p _ => do
    next (← parts p (← bodyAt (app (root ++ `native_factor_statement) p)))

/-- Every output is closed and checked by the ordinary kernel. -/
private def save (name : Name) (p : Array Expr) (proof target : Expr)
    (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type, value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "raw baseline bridge: unresolved original operand in {name}"
    let missing := e.getUsedConstants.filter fun key => (env.find? key).isNone
    unless missing.isEmpty do
      throwError "raw baseline bridge: missing original private metadata {missing.toList}"
  let (type, value) := Lean.ShareCommon.shareCommon (type, value)
  IO.println s!"Kernel checking SAME raw baseline bridge {name}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .regular 0, safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  addDocStringCore name "Exact native-to-named equality for the SAME original unscaled raw baseline and outer node. Only the original retained-leading regularity and outer-weight admission are used; no new source, phase, profile, corrected differential premise or inner angular guard is introduced (main:eq:primary-strain; app:ch_waves:eq:individual-representation)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "raw baseline bridge: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS SAME raw baseline bridge {name}/{p.size}: {axioms}"

private def publishNative (statement : Bool) : MetaM Unit :=
  withNative fun p proof target => do
    if statement then
      save (root ++ `native_factor_statement) p target (mkSort .zero) true
    else
      save (root ++ `native_factor) p proof (app (root ++ `native_factor_statement) p)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge.Template
end
