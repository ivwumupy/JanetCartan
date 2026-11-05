module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Basic
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Template
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.StatementTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

/-! The exact existing aggregation node premise at the common two-quadrature
price. This is a proposition definition, with no new estimate assumed
(`main:eq:primary-strain`). -/

open Lean Meta
open JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
open NodeUniformTransfer.Template

run_meta do
  DataTemplate.withData fun d =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q =>
      withLocalDeclNoLocalInstanceUpdate `C .default (mkConst ``Real) fun C => do
        let nonneg ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,C]
        withLocalDeclNoLocalInstanceUpdate `hC .default nonneg fun hC => do
          let n := mkApp (mkConst ``Nat.succ) d.native[0]!
          let S := app ``JanetCartan.UniformStep.projectedStressResidualConstant #[n,d.native[1]!]
          let cost ← mkAppM ``HMul.hMul #[S,← mkAppM ``HAdd.hAdd #[C,C]]
          let costNonneg := app (root ++ `node_coefficient_nonneg) #[n,d.native[1]!,C,hC]
          let target ← NodeStatementTemplate.requirement d q cost costNonneg
          let params := d.args ++ #[q,C]
          unless params.size == 56 do throwError "node uniform transfer: exact node boundary changed"
          save `node_strain_statement params target (mkSort .zero) true

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.node_strain_statement
