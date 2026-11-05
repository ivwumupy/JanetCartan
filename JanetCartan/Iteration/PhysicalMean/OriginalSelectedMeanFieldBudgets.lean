module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanFieldProfilesTemplate
import all JanetCartan.Iteration.PhysicalBackground.NativeBaseProfiles

/-!
# The actual original mean's fixed geometric initial reach

Publish the SAME native wide-field geometry before any raw source budget,
finite Picard index, smoothing order, target, or history. The actual Picard
budget and full initialized field are instantiated in the separate profile
leaf (`main:prop:mean`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
open Lean Elab Command
open JanetCartan
open JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfilesTemplate
run_cmd liftTermElabM do publishUniformActual
run_cmd liftTermElabM do publishUniformChoice 0
run_cmd liftTermElabM do publishUniformChoice 1
run_cmd liftTermElabM do publishUniformChoice 2
end

#print axioms JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.uniform_raw_exists
#print axioms JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.SfullW
#print axioms JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.two_le_SfullW
#print axioms JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.raw_profile_exists
