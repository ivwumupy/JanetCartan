module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularData
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticCoordinates
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# Exact native coordinates for the original raw angular derivative

The bridge only names intermediate equalities on the original actual53
parameter spine. Its consumer is the already fixed
`Actual.unprefixed_forward_statement`, used by the primary source
factorization (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template

open Lean Meta Elab Command
open OriginalRawPrimaryRealizationApplication
open OriginalRawAngularActualApplication

def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge
def native := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Native
def actual := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Actual
def app (key : Name) (args : Array Expr) : Expr := mkAppN (mkConst key) args

/-- The same actual source/node53, its native65 coordinates and the unchanged
refined input, physical point and original source membership. -/
def withNode (go : Array Expr → Array Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  actualTelescope (← getConstInfo `JanetCartan.PhysicalMean.OriginalCanonicalActual.G).type fun p _ => do
    let original ← bodyAt (app `JanetCartan.PhysicalMean.OriginalCanonicalActual.G p)
    unless original.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.G 65 do
      throwError "raw angular bridge: the original native parameter spine changed"
    let nativeParams := original.getAppArgs
    let producer := app (native ++ `raw_full_forward_on_source) nativeParams
    forallBoundedTelescope (← inferType producer) (some 3) fun tail _ => do
      unless tail.size == 3 do
        throwError "raw angular bridge: missing original input, point or source membership"
      go p nativeParams tail (mkAppN producer tail)

/-- Publish only a closed checked intermediate, with its exact original
domains. This does not change any numerical or analytic premise. -/
def save (key : Name) (p : Array Expr) (value target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "raw angular bridge: unresolved original field in {key}"
    let missing := e.getUsedConstants.filter fun c => (env.find? c).isNone
    unless missing.isEmpty do
      throwError "raw angular bridge: missing original private metadata in {key}: {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking raw angular bridge {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Exact intermediate equality for the SAME original raw angular derivative, full phase, mask and annular amplitude. No analytic premise, new input or corrected response is introduced (main:eq:primary-strain)."
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "raw angular bridge: nonstandard axioms in {name}: {ax}"
  logInfo m!"Raw angular bridge {key}/{p.size}: {ax}"

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template
end
