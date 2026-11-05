module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.PhaseExtension.Basic
public import JanetCartan.Analysis.Microlocal.FourierIntegral.PhaseExtension.NormalGeometry
public import JanetCartan.Analysis.Microlocal.FourierIntegral.PhaseExtension.Realization

/-!
# A locally defined phase in the actual low graph construction

For `app:ch_regular_base:thm:actual-calculus`, Step 1,
`exists_smooth_phase_extension` constructs a globally smooth auxiliary phase
agreeing on a neighborhood of a closed buffered chart. The chart may be
unbounded in frequency. `graphOperator_phase_congr` and
`crossNormalKernel_phase_congr` preserve the literal kernels on their supports.
The full averaged-gradient image, inverse equations, primitive support geometry
and all phase jets on the chart are unchanged.

`exists_graphL2_of_local_phase` applies the actual low construction to this
extension. It constructs the bounded graph with original-phase test and Schwartz
realizations, strong forward and adjoint convergence, exact right-frequency
factorizations, and uniqueness. Its constant precedes the amplitude and the
auxiliary extension. Global continuity of the original phase is not a premise.

The original geometric buffer and all normalized Jacobian/inverse/symbol jets
remain explicit primitive hypotheses. In particular the inverse jets are on
every shell of the whole averaged-gradient image, not a smaller common target.
The auxiliary extension is not asserted to be globally homogeneous or to obey
global symbol bounds; only its agreement on the supported chart is used.
-/
