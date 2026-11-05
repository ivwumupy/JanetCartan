module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.HistoryScale
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Representative.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Representative.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles
import all JanetCartan.Iteration.PhysicalPrimary.OriginalPrimarySourcePhaseGeometry
import all JanetCartan.Iteration.PhysicalPairs.OriginalMaskGeometry
import all JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate

/-!
# Global smooth representatives of the original ordinary primary phase

The negative Sobolev source estimates need a globally smooth phase. The actual
original finite-menu construction supplies it, with the same ordinary
`group_phase` germ on the entire source chart. Its first derivative and every
higher spatial derivative retain the original prehistory price and true
history scale; its gradient lies in the original `Ksource22` there.

These are actual original-data instances for
`PhysicalPairs.OriginalNegativeRows.geometry` and `exists_price`, with no
assumed global smoothness of the raw phase (`main:eq:primary-strain`,
`app:ch_regular:eq:source-tail` in paper-v2). No source or cutoff is changed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

run_meta JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.RepresentativeTemplate.publish 0
run_meta JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.RepresentativeTemplate.publish 1
run_meta JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.RepresentativeTemplate.publish 2
run_meta JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.RepresentativeTemplate.publish 3
run_meta JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.RepresentativeTemplate.publish 4
run_meta JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.RepresentativeTemplate.publish 5
run_meta JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.RepresentativeTemplate.publish 6
run_meta JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.RepresentativeTemplate.publish 7
run_meta JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.RepresentativeTemplate.publish 8
