module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.RawSource
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeContext
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.RawSource
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# The value of the original admitted primary tensor

The original `SourceData.tensor` already contains its compact-source admission.
Its value is the real part of the same full raw-source quadrature. This leaf
retains that function identity for the original native53 inputs and final
quadrature Boolean, without reconstructing the admission or inserting a cutoff.

Consumers: the symmetry input of `StrainTransfer.NativeTensor` and the real and
imaginary tensor identities in `StrainTransfer.NativeNorms`, hence the same-node
strain bound (`main:eq:lag-strain`, `main:eq:primary-strain` in paper-v2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.TensorData

open Lean Meta Elab Command

private def rawRoot := `JanetCartan.PhysicalPrimary.OriginalRawSourceField
private def targetName :=
  `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.native_tensor_value

private def app (name : Name) (p : Array Expr) := mkAppN (mkConst name) p

private def bodyAt (e : Expr) : MetaM Expr := do
  let info ← getConstInfo e.getAppFn.constName!
  let some value := info.value? (allowOpaque := true) |
    throwError "original tensor value: missing saved body {info.name}"
  return ((value.instantiateLevelParams info.levelParams e.getAppFn.constLevels!).beta
    e.getAppArgs).headBeta

run_meta do
  NativeContext.withSource fun c => do
    let p := c.params
    unless p.size == 54 do throwError "original tensor value: original native54 changed"
    let tensorBody ← bodyAt c.tensor
    unless tensorBody.isAppOfArity ``Subtype.mk 4 do
      throwError "original tensor value: the saved tensor is not its admitted Subtype.mk"
    let tensorArgs := tensorBody.getAppArgs
    let valueType := tensorArgs[0]!
    let value := tensorArgs[2]!
    unless value.isAppOfArity ``DFunLike.coe 6 do
      throwError "original tensor value: the saved real-part application changed"
    let realArgs := value.getAppArgs
    unless realArgs[4]!.isAppOfArity ``ResponseSourceExtension.tensorFieldRealPart 1 do
      throwError "original tensor value: not the original tensor-field real part"
    let rotated := realArgs[5]!
    unless rotated.isAppOfArity ``HSMul.hSMul 6 do
      throwError "original tensor value: the saved quadrature scalar action changed"
    let rotatedArgs := rotated.getAppArgs
    unless rotatedArgs[4]! == app ``quadratureScalar #[p[53]!] &&
        rotatedArgs[5]! == c.tensorField do
      throwError "original tensor value: changed Boolean or original native raw source"
    let actualSource := app (rawRoot ++ `source) p[:53].toArray
    unless (← bodyAt actualSource) == c.tensorField do
      throwError "original tensor value: actual53 and native69 are different raw sources"
    let actualRotated := mkAppN rotated.getAppFn (rotatedArgs.set! 5 actualSource)
    let rhs := mkAppN value.getAppFn (realArgs.set! 5 actualRotated)
    let conclusion := mkAppN (mkConst ``Eq [.succ .zero])
      #[valueType, c.quadrature, rhs]
    let proof := mkAppN (mkConst ``Eq.refl [.succ .zero]) #[valueType, rhs]
    let type ← instantiateMVars (← mkForallFVars p conclusion)
    let proof ← instantiateMVars (← mkLambdaFVars p proof)
    let env ← getEnv
    for e in #[type, proof] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
          e.hasLooseBVars || e.hasSorry then
        throwError "original tensor value: unresolved input in the native54 equality"
      let missing := e.getUsedConstants.filter fun name => (env.find? name).isNone
      unless missing.isEmpty do
        throwError "original tensor value: missing original metadata {missing}"
    let (type, proof) := Lean.ShareCommon.shareCommon (type, proof)
    IO.println "Kernel checking original admitted tensor value/54"
    (← IO.getStdout).flush
    addDecl (.thmDecl {name := targetName, levelParams := [], type, value := proof})
      (forceExpose := true)
    addDocStringCore targetName "The value of the SAME SourceData.tensor54 is exactly tensorFieldRealPart (quadratureScalar q • OriginalRawSourceField.source53). The original native53 parameters and final quadrature Boolean are unchanged, and the existing compact-source admission is reused. Consumers: NativeTensor symmetry and NativeNorms real/imaginary source identities (main:eq:lag-strain; main:eq:primary-strain)."
    let axioms ← collectAxioms targetName
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "original tensor value: nonstandard axioms {axioms}"
    logInfo m!"PASS original admitted tensor value/54: {axioms}"

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.TensorData
end

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.native_tensor_value
