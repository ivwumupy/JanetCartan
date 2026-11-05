module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.RootStability.Assembly
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.RootStability.BranchUniqueness

/-!
# Finite-order stability of actual transverse roots

For `app:lem:common-hamilton-phase`, actual smooth roots on a fixed compact
inner parameter ball depend locally Lipschitz continuously in `C^m` on the
equation in `C^m`, with a separate fixed `C¹` gap neighborhood. Subtracting the
differentiated equations gives the higher-jet induction, and scalar uniqueness
identifies all jets of independently constructed branches. The parent phase
construction supplies the common cylinder, reference root and gap, using
`exists_uniform_C1_stable_sectionRoot` and
`exists_sectionEnergy_finiteOrder_bound` on normalized state domains.
-/
