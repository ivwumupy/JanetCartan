module

public import JanetCartan.Iteration.PhysicalSampling.OriginalBareScale

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Uniform
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Statement
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.SourceIdentity
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.FrequencyIdentity

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.ProofTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Uniform
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Statement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.SourceStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.FrequencyStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.SelectedStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeFinalStatement
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! Specialize the native paired-source node theorem to the same selected
source. The original BareScale producer discharges its numeric frame bound;
the independently proved exact predicate identities retain the original
source and node statements (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.SelectedPairedTemplate
open Lean Meta
open JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
open NodeUniformTransfer.Template

def publishConditional : MetaM Unit := do
  DataTemplate.withData fun d =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q =>
      withLocalDeclNoLocalInstanceUpdate `C .default (mkConst ``Real) fun C => do
        let nonneg ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,C]
        withLocalDeclNoLocalInstanceUpdate `hC .default nonneg fun hC => do
          let p56 := d.args ++ #[q,C]
          let paired := app (root ++ `paired_discrepancy_bound) p56
          withLocalDeclNoLocalInstanceUpdate `hPaired .default paired fun hPaired => do
            let glue := primaryRoot ++ `NodeSelectedNativeGlue
            withLocalDeclNoLocalInstanceUpdate `hPairEq .default
                (app (glue ++ `paired_statement) p56) fun hPairEq =>
              withLocalDeclNoLocalInstanceUpdate `hNodeEq .default
                  (app (glue ++ `node_statement) p56) fun hNodeEq => do
                let hNative ← mkAppM ``Eq.mp #[hPairEq,hPaired]
                let hGamma := app `JanetCartan.PhysicalSampling.OriginalBareScale.γ_le_ambient
                  d.native[:24].toArray
                let comparison := app (transferRoot ++ `native_node_strain_le_discrepancies) d.sourceArgs
                let .forallE _ frameType _ _ := (← inferType comparison).consumeMData |
                  throwError "selected node transfer: original native frame boundary changed"
                unless ← isDefEq (← inferType hGamma) frameType do
                  throwError "selected node transfer: BareScale does not supply the SAME original tolerance"
                let native := app (root ++ `native_node_of_paired_discrepancy)
                  (d.sourceArgs ++ #[q,C,hC,hGamma,hNative])
                let proof ← mkAppM ``Eq.mpr #[hNodeEq,native]
                let p := d.args ++ #[q,C,hC,hPaired,hPairEq,hNodeEq]
                unless p.size == 60 do throwError "selected node transfer: additional input entered"
                save `node_of_paired_with_statement_equalities p proof (app (root ++ `node_strain_statement) p56) false

/-- Supply both exact original-data predicate identities in the selected theorem. -/
def publishFinal : MetaM Unit := do
  let internal := root ++ `node_of_paired_with_statement_equalities
  openRaw 58 (← getConstInfo internal).type fun p => do
    let statementArgs := p[:56].toArray
    let glue := primaryRoot ++ `NodeSelectedNativeGlue
    let pairEq := app (glue ++ `paired_eq) statementArgs
    let nodeEq := app (glue ++ `node_eq) statementArgs
    let proof := app internal (p ++ #[pairEq,nodeEq])
    save `node_of_paired_discrepancy p proof
      (app (root ++ `node_strain_statement) statementArgs) false

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.SelectedPairedTemplate
end
