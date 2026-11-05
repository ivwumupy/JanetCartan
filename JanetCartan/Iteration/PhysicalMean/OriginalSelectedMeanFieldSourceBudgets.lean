module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanFieldCurrentTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardBudgets
import all JanetCartan.Iteration.PhysicalBackground.NativeBaseProfiles
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity

/-! # Actual before-history full initialized mean coefficients

The COMMON full-source Picard coefficient determines the raw and full-field
budgets, not the geometric initial reach. All choices precede the physical
history and target (`main:prop:mean`). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open JanetCartan
public meta section
open Lean Elab Command
open JanetCartan.PhysicalMean.OriginalSelectedMeanFieldCurrentTemplate
run_cmd liftTermElabM do publishRawBudget false
run_cmd liftTermElabM do publishRawBudget true
run_cmd liftTermElabM do publishFieldExists
run_cmd liftTermElabM do publishFieldChoice 0
run_cmd liftTermElabM do publishFieldChoice 1
run_cmd liftTermElabM do publishFieldChoice 2
end
#print axioms JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.Craw
#print axioms JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.Craw_nonneg
#print axioms JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.exists_CW
#print axioms JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.CW
#print axioms JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.CW_nonneg
#print axioms JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.CW_continuation
