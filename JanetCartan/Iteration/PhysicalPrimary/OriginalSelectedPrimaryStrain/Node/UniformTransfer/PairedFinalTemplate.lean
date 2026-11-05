module

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

/-! Supply the paired source premise from the exact admitted-label bound.
The final statement retains only the original full-family discrepancy
hypothesis and its nonnegative price (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.PairedFinalTemplate
open Lean Meta
open JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
open NodeUniformTransfer.Template

/-- Both quadratures are supplied by the same original full-family premise. -/
def publish : MetaM Unit := do
  withOperator fun d hOp =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q =>
      withLocalDeclNoLocalInstanceUpdate `C .default (mkConst ``Real) fun C => do
        let nonneg ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,C]
        withLocalDeclNoLocalInstanceUpdate `hC .default nonneg fun hC => do
          let uniform := app (root ++ `uniform_discrepancy_bound) (d.fixed ++ #[q,C])
          withLocalDeclNoLocalInstanceUpdate `hDiscrepancy .default uniform fun hUniform => do
            let paired ← withLocalDeclNoLocalInstanceUpdate `imaginary .default
                (mkConst ``Bool) fun quad => do
              let p := d.fixed ++ #[q,C,hUniform] ++ d.selected[33:].toArray ++
                #[d.hAux,hOp,d.sample,quad]
              let proof := app (root ++ `admitted_discrepancy_bound) p
              mkLambdaFVars #[quad] proof
            let proof := app (root ++ `node_of_paired_discrepancy)
              (d.args ++ #[q,C,hC,paired])
            let p := d.fixed ++ #[q,C,hC,hUniform] ++ d.selected[33:].toArray ++
              #[d.hAux,hOp,d.sample]
            unless p.size == 60 do
              throwError "node uniform transfer: final original input boundary changed"
            save `node_of_uniform_discrepancy p proof
              (app (root ++ `node_strain_statement) (d.args ++ #[q,C])) false

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.PairedFinalTemplate
end
