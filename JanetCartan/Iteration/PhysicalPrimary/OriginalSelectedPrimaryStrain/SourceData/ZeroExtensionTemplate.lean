module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceDataTemplate
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData.ZeroExtensionBasic
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! # The literal primary inverse input on the whole ambient space

This retains the original single source cutoff and the actual input map of
the full uncut response. Consumer: the primary first-mask realization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceDataTemplate

open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def world := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p

private def inputTelescope (type : Expr) (next : Array Expr → MetaM Unit) : MetaM Unit :=
  loop 54 type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0,_,p => next p
    | k+1,type,p => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "actual primary zero extension: source54 telescope changed"
      let domain := domain.instantiateRev p
      if bi == .instImplicit then
        withLocalDecl name bi domain fun x => loop k body (p.push x)
      else
        withLocalDeclNoLocalInstanceUpdate name bi domain fun x => loop k body (p.push x)

elab "extend_actual_primary_source_input" : command => liftTermElabM do
  let ci ← getConstInfo (root ++ `input)
  inputTelescope ci.type fun p => do
    let value := ((ci.value! (allowOpaque := true)).beta p).headBeta
    let some mapper := value.find? (·.isAppOfArity
        `JanetCartan.PhysicalPrimary.OriginalSourceDiscrepancy.tensor_input 38) |
      throwError "actual primary zero extension: original tensor-input map disappeared"
    let weak := mapper.getAppArgs
    let fixed := weak[:23].toArray
    let hχ := app (masks ++ `χ₂_smooth) fixed
    let χ := (← inferType hχ).appArg!
    let S ← mkAppM ``tsupport #[χ]
    let W := app (world ++ `W) fixed
    let hW := app (world ++ `W_measurable) fixed
    let hSW ← mkAppM ``Set.Subset.trans
      #[app (masks ++ `χ₂_support_chart) fixed,app (regular ++ `hUW) fixed]
    let Q := app (regular ++ `Current.Q) weak
    let η := (← inferType (app (masks ++ `χsrc_smooth) fixed)).appArg!
    let tensor := app (root ++ `tensor) p
    let u ← mkAppM ``Subtype.val #[app (root ++ `input) p]
    let proof := app (root ++ `zeroExtend_tensor_input_of_ae)
      #[mkApp (mkConst ``Nat.succ) p[0]!,S,W,Q,η,tensor,u,hW,hSW,
        app (root ++ `input_ae) p]
    let type ← instantiateMVars (← mkForallFVars p (← inferType proof))
    let value ← instantiateMVars (← mkLambdaFVars p proof)
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
        throwError "actual primary zero extension: unresolved source operand"
    let (type,value) := Lean.ShareCommon.shareCommon (type,value)
    let name := root ++ `input_zeroExtend
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
    addDocStringCore name "The SAME actual primary input's zero extension equals its single-cutoff stress representative. The support inclusion and local representative are derived from the actual source data, without a second χ₂ (main:eq:primary-strain)."
    let ax ← collectAxioms name
    unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "actual primary zero extension: nonstandard axioms {ax}"
    logInfo m!"PASS actual primary input_zeroExtend/{p.size}: {ax}"

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceDataTemplate
end

