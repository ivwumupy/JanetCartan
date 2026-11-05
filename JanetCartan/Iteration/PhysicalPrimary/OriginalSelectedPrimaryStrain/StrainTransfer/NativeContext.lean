module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceDataTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawCombinedNative
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceDataTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalGraphResponse
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! The exact published tensor54 data for the original source-to-strain
transfer. Only original metadata is read; compact-source admission is reused
from SourceData (main:eq:lag-strain; main:eq:primary-strain). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeContext
open Lean Meta

private def dataRoot := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
private def raw := `JanetCartan.PhysicalPrimary.OriginalRawSourceField.Native
private def response := `JanetCartan.PhysicalSampling.OriginalGraphResponse
private def app (key : Name) (p : Array Expr) : Expr := mkAppN (mkConst key) p

private def bodyAt (e : Expr) : MetaM Expr := do
  let ci ← getConstInfo e.getAppFn.constName!
  let some value := ci.value? (allowOpaque := true) |
    throwError "actual primary strain transfer: missing original body {ci.name}"
  return ((value.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta

private def publishedTelescope (count : Nat) (type : Expr)
    (next : Array Expr → MetaM Unit) : MetaM Unit := loop count type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0,_,p => next p
    | k+1,type,p => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "actual primary strain transfer: published source telescope ended at {p.size}"
      let domain := domain.instantiateRev p
      if bi == .instImplicit then
        withLocalDecl name bi domain fun x => loop k body (p.push x)
      else
        withLocalDeclNoLocalInstanceUpdate name bi domain fun x => loop k body (p.push x)

/-- Read the already admitted tensor, keeping the shared original source
context. No compact-source admission proof is reconstructed by this consumer. -/
def withSource (next : SourceDataTemplate.Context → MetaM Unit) : MetaM Unit := do
  publishedTelescope 54 (← getConstInfo (dataRoot ++ `tensor)).type fun p => do
    let sourceArgs := p[:53].toArray
    let old := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
    let combined ← bodyAt (app (old ++ `selectedSourceCombinedWave) sourceArgs)
    unless combined.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalLocalWaves.Combined.field 69 do
      throwError "actual primary strain transfer: original combined raw69 changed"
    let rawArgs := combined.getAppArgs
    let tensorField := app (raw ++ `source) rawArgs
    let sourceBody ← bodyAt tensorField
    unless sourceBody.isAppOfArity `JanetCartan.CorrectedAtoms.complexAtomicSource 5 do
      throwError "actual primary strain transfer: original raw tensor source changed"
    let sm ← bodyAt (app (old ++ `selectedSourceCombinedWave_smooth) sourceArgs)
    unless sm.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalLocalWaves.Combined.active_smooth 70 do
      throwError "actual primary strain transfer: original raw smooth70 changed"
    let eq ← inferType (app (raw ++ `combined_eq_corrected_raw) sm.getAppArgs)
    unless eq.isAppOfArity ``Eq 3 && eq.getAppArgs[2]!.isAppOfArity
        `JanetCartan.CorrectedAtoms.complexCorrectedAtom 6 do
      throwError "actual primary strain transfer: original full corrected atom changed"
    let correction := eq.getAppArgs[2]!.getAppArgs
    let sa := sourceBody.getAppArgs
    unless sa[2]! == correction[2]! && sa[3]! == correction[3]! && sa[4]! == correction[5]! do
      throwError "actual primary strain transfer: different raw/current/cutoff operands"
    let B := correction[4]!
    unless B.isAppOfArity (response ++ `B) 42 do
      throwError "actual primary strain transfer: original graph42 response changed"
    let fullB ← bodyAt B
    unless fullB.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalFullResponse.B 38 do
      throwError "actual primary strain transfer: full uncut response38 changed"
    let tensor := app (dataRoot ++ `tensor) p
    next {
      params := p, graph := B.getAppArgs, weak := fullB.getAppArgs,
      rawArgs := rawArgs, rawSmoothArgs := sm.getAppArgs,
      F := sa[2]!, rawWave := sa[4]!, tensorField := tensorField,
      quadrature := ← mkAppM ``Subtype.val #[tensor], tensor := tensor,
      input := app (dataRoot ++ `input) p }


end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeContext
end
