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

/-! One admitted original quadrature inherits the full-family discrepancy
bound with the identical source and carrier. Consumer: the primary node
strain assembly (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.PointwiseTemplate
open Lean Meta
open JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
open NodeUniformTransfer.Template

/-- Retain the original source-bound statement or its exact admitted-label proof. -/
def publish (statement : Bool) : MetaM Unit := do
  withOperator fun d hOp =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q =>
      withLocalDeclNoLocalInstanceUpdate `C .default (mkConst ``Real) fun C =>
        withLocalDeclNoLocalInstanceUpdate `imaginary .default (mkConst ``Bool) fun quad => do
          let statementArgs := d.args ++ #[quad,q,C]
          unless statementArgs.size == 57 do
            throwError "node source bound: original selected/source boundary changed"
          let named := app (root ++ `admitted_discrepancy_bound_statement) statementArgs
          if statement then
            let comparison := app (transferRoot ++ `selected_node_strain_le_discrepancies) d.args
            forallBoundedTelescope (← inferType comparison) (some 2) fun point _ => do
              let source := mkApp (app (sourceRoot ++ `discrepancy) (d.sourceArgs.push quad)) point[0]!
              let norm ← mkAppM ``Norm.norm #[source]
              let price ← mkAppM ``HMul.hMul #[C,← decayAt (← rhoAt d) q]
              let bound ← mkAppM ``LE.le #[norm,price]
              let target ← mkForallFVars point bound
              save `admitted_discrepancy_bound_statement statementArgs target (mkSort .zero) true
          else
            let uniform := app (root ++ `uniform_discrepancy_bound) (d.fixed ++ #[q,C])
            withLocalDeclNoLocalInstanceUpdate `hDiscrepancy .default uniform fun hUniform => do
              forallBoundedTelescope (← bodyAt named) (some 2) fun point _ => do
                let proof ← ProofTemplate.normalizedBound d hOp q C hUniform point quad
                let p := d.fixed ++ #[q,C,hUniform] ++ d.selected[33:].toArray ++
                  #[d.hAux,hOp,d.sample,quad]
                unless p.size == 60 do
                  throwError "node source bound: new data or analytic premise entered"
                save `admitted_discrepancy_bound p (← mkLambdaFVars point proof) named false

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.PointwiseTemplate
end
