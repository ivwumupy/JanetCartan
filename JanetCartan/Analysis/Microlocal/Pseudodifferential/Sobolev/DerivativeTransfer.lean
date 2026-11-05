module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Phase
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.SourceIntegration
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.OperatorIteration

/-!
# Derivative transfer for scalar two-position amplitudes

Derivative transfer for `app:ch_regular_base:eq:graph-derivative-transfer`
and the gain-one argument in `app:ch_regular_base:eq:fio-input`, for phase `x · ξ`:

* source integration by parts on compact smooth data;
* physical coordinate identifications and the first phased amplitude derivative;
* support, smoothness and finite primitive derivative budgets of the modified amplitudes;
* actual single-coordinate distributional identities through strong frequency limits;
* finite ordered expansions for the full integral and its bounded L² realization.

The expansion has `2 ^ s` branches, counted with multiplicity. A term with `k`
datum derivatives uses exactly `s - k` transfer steps and at most `s - k` extra
primitive physical derivatives. All derivatives act on the complete amplitude,
including both physical positions and their masks. Only finite primitive budgets
are hypotheses; the operator identities and their required integrability are proved.
-/
