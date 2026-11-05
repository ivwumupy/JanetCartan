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

/-! The full original observed-family discrepancy premise. Its price and
accuracy are fixed before every history, target, smoothing or sample input
(`main:eq:primary-strain`). -/

open Lean Meta
open JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
open NodeUniformTransfer.Template

run_meta do
  withOperator fun d _ =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q =>
      withLocalDeclNoLocalInstanceUpdate `C .default (mkConst ``Real) fun C => do
        let comparison := app (transferRoot ++ `selected_node_strain_le_discrepancies) d.args
        forallBoundedTelescope (← inferType comparison) (some 2) fun point _ => do
          let hypothesis ← uniformType d q C point
          save `uniform_discrepancy_bound (d.fixed ++ #[q,C]) hypothesis (mkSort .zero) true

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.uniform_discrepancy_bound
