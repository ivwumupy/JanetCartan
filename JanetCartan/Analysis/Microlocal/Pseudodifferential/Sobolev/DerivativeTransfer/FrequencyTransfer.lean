module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.FrequencyTransfer.FullWeak

/-!
# Single-coordinate derivative transfer through frequency integration

For `app:ch_regular_base:eq:graph-derivative-transfer`, the actual full operator
and its L² realization satisfy the single-coordinate distributional transfer
identity on compact smooth input. For `app:ch_regular_base:eq:fio-input`, an
order-minus-one weighted primitive budget identifies the first output derivative
with the output-derivative amplitude operator.

Compact-frequency Fubini and integration by parts are justified by compact
supports. The identities pass through the existing strong L² limit using the
continuous embedding into tempered distributions. Finite primitive physical
budgets discharge source integrability and identify the limit with the literal
source-first full integral; output integrability is proved rather than assumed.
-/
