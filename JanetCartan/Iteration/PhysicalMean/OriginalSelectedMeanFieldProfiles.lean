module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanFieldSourceBudgets
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanFieldApplication
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicard
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardBudgets
import all JanetCartan.Iteration.PhysicalBackground.NativeBaseProfiles
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Full initialized mean field and full strain from the actual source

The original initializer, same positive-current inverse, common full-source
Picard profile and fixed geometric reach supply every analytic input. The
coefficient is fixed on selected33 and N, before history or target DATA. The
only remaining hypotheses are the genuine INITIAL auxiliary and full-field
reach gates (`main:prop:mean`, `main:eq:mean-normal-field`). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
open Lean Elab Command
open scoped Matrix.Norms.Frobenius
open JanetCartan.PhysicalMean.OriginalSelectedMeanFieldApplication
run_cmd liftTermElabM do publishRaw
run_cmd liftTermElabM do publishField
end
#print axioms JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.initializedRaw_profile
#print axioms JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.initializedField_strain_profile
