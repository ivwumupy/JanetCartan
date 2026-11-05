module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.Profiles
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FirstMaskTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Smoothness of both actual primary raw amplitudes

The same full-forcing amplitude profile proves smoothness for both
quadratures on the original source chart. This first-mask input is
independent of the source-norm price (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
open Lean Meta Elab Command
open JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate

run_cmd liftTermElabM do
  withFamily fun c => do
    let proof ← c.family (.proj ``And 0 (← commonProfile c))
    save `B_smooth c.fixed proof (← inferType proof)
end

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.B_smooth
