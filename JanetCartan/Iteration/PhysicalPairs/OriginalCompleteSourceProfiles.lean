module
public meta import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteSourceProfilesTemplate
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
profile_original_complete_source_amplitude
open Lean Meta Elab Command
run_meta do
  let name := `JanetCartan.PhysicalPairs.OriginalCompleteSourceProfiles.source_jets
  let _ ← getConstInfo name
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual physical source jets have nonstandard axioms: {axioms}"
  logInfo m!"actual physical D, same complete source profile, genuine R-jets: {axioms}"
