module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.InitialBuffer
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.ChartCutoff
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Definitions
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.KernelAgreement
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Profiles

/-!
# Primitive amplitude inputs for the canonical adjoint

The fixed initial and chart cutoffs are chosen before the immersion and
initial scalar. `InitialBuffer` derives containment of the actual supported
footpoints from the retained inverse-flow identities and estimates. Its
initial cutoff uses only the original scalar norm domain. `KernelAgreement`
uses Hamilton conservation to prove that the fixed extensions represent the
same literal canonical kernel.

`exists_canonical_amplitude_profiles` assembles the scalar, flow, geometric
and fixed frequency profiles for the SAME kernel. Its geometric buffers and
footpoint containments are derived from fixed primitive data, and its analytic
inputs are retained outputs of `exists_projected_local_positive_amplitude`.
The six profiles share one high immersion norm and one high original scalar
norm, with reserve `2*(n+1)+13`, including order zero. Global smoothness and
the original support are proved as well.

These supply the amplitude inputs of
`exists_scalarTransportCarrierAdjoint_periodic_raw_bound`
(`app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-T`,
`app:ch_waves:eq:joint-tame`). The fixed angular neighborhood and radial
smoothness are supplied by `adjointAngularGraph_neighborhood` and
`scaled_halfOrderRadialFactor_contDiff`; `fixed_frequency_supports_compact`
supplies the endpoint's compact sets. The phase, graph, gap and trade inputs
come from `PhaseExtension`. Finite-family selection and the operator endpoint
application remain with the canonical adjoint consumer.
-/
