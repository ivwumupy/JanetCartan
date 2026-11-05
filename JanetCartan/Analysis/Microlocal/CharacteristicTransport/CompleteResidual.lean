module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.Endpoint
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.PdoAction
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.StrongLimits
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.Reality
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.UncutIdentity
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.TransportColumns
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.OperatorIdentity
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.LocalL2

/-!
# The direct complete residual: finite identity, operator limits and reality

Source: `paper-v2.tex`, `app:ch_regular_base:eq:energy-complete-residual`.
Consumers: the direct regular-sector construction and
`FixedDomainInverse.exact_physical_localSobolev_ae`.

`firstOrderApply_cutDirectSolver` combines the literal retarded derivative,
phase diagonal, leading endpoint and complement equation into the complete
finite-cutoff identity. Its residual has exactly the three terms
Op(A_t W₁(t,t) β), E_(P W₁) Bβ, and (1/i) Op(P_x(b₋₁ α)). The output
commutator acts on the whole solver core; the plateau corollary removes it
only under a neighborhood equality χout = 1. Op(α), with α = σ β and all
low frequencies, is retained. No theorem identifies it with the identity.

`MaskedKernels` matches the solver to the published fixed-slab and physical
retarded regularizations plus the canonical graph PDO. Both pieces use the
same frequency cutoff, output mask and original right source mask. The fixed
slab comparison retains its lower buffer and both time endpoints.

`completeResidual_test_and_ae_of_component_limits` derives the uncut tested
equation from six separate L² regularization outputs, using the proved finite
identity. It also gives the AE equation when the very same output has an
actual weak derivative. It does not assume a successful uncut solver equation
or differentiate an L² limit pointwise.

`completeResidual_operators_of_graph_regularizations` instantiates that passage
with the actual retarded constructor and four canonical graph PDOs. It
constructs both retarded operators from the finite forward/adjoint graph
realizations, LOW bounds and strong limits, retains their literal adjoint
integrals, and proves the equation for every L² source by density. The same
original source mask appears in all six components. `Regularity` derives
joint smoothness of P W₁ and preservation of its lower source-time buffer
from the original coefficients and W₁.

`SectorEquations` propagates the resulting tested equations through finite
sums, the physical plus pairing and its existing real compression. It proves
the paired local a.e. equation for the same output's weak derivative. These
are deductions from constructed sector equations, not assertions that their
actual chart inputs have been instantiated.

The actual producer instantiation is still unfinished. The primitive inputs
and their producers are:

* `Characteristic.exists_physical_pencil_kernel` constructs the local physical
  phase, leading/correction columns, diagonal data and cancellation, with B₀
  and the actual coordinate split. `TransportColumns` identifies P W₁ with
  its physical column derivatives and derives the finite theorem's column
  premise from the direct-correction/null-transport identities. Pulling the
  actually selected physical chart into the canonical time-space kernel and
  extending through its supported margins remain instantiation obligations.
* `Characteristic.complementInverse_identity` proves H b₋₁ = I - Π on its
  actual completion determinant domain; `leading_endpoint_add_complementInverse`
  checks its algebraic cancellation with A_t k lᵀ σ β. The actual off-root
  pencil symbol and multiplier support must instantiate this same inverse.
* `KernelDifferentiation.firstOrderApply_cut_elapsedGraphIntegral` and its
  retarded-column leaf prove differentiation with the upper endpoint and
  output mask. `FiniteIdentity` assembles this with the physical PDO action.
* `EvolutionIntegral.KernelIdentification.exists_retardedOperator_of_regularizations`
  constructs the same forward elapsed integral and literal reversed-triangle
  adjoint, with a.e. finite representatives and strong limits, from the
  primitive graph realization outputs. Its exact retarded representatives are
  identified in `MaskedKernels`.
* `FourierIntegral.exists_fullGraphFamily_of_wholeImage_phase`, specialized
  to the canonical phase and each full masked PDO symbol, exports exactly
  the four finite representatives and common-cutoff limits consumed by
  `OperatorIdentity`. Their primitive budget instantiation remains explicit.
  The matrix PDO integer estimate producer uses another normalization and
  regularization API; identifying its operators with these canonical physical
  graphs remains necessary when applying those estimates. The sharp-ball
  limits in `AmplitudeBound.exists_matrixTwoPositionAmplitudeOperator` alone
  do not supply the common smooth cutoff sequence.
* Graph/PDO H¹ estimates supply the uncut output's weak derivative on smooth
  source data. Its same-history instantiation remains with the sector parent.

`Reality` constructs the physical plus-paired finite sum and its existing real
compression, retaining the literal adjoint; `SectorEquations` proves their
tested and a.e. equations from the individual sector equations. Selecting
the actual finite chart family and supplying those individual constructions
remain assembly obligations.
Common finite-family masks, uniform symbol budgets, all forward/literal-adjoint
bounds and actual history instantiation remain with the regular-sector parent.
The conditional identities here do not prove unconditional sector existence
or the main theorem.
-/
