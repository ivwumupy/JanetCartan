module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.RealCommutator.Representation

/-!
# Transfer of higher commutators to the real continuum normal

Checked Sobolev value maps, compatibility with the shared L² coordinate
isometry, ordered weak derivatives, and literal real compression for
`app:ch_background:eq:bg-commutator` and `app:ch_background:prop:bg-inverse`.
The fixed exterior commutator is constructed from the existing Leibniz operator.
The finite assembly preserves all real weights, including the carrier weight four,
and retains the additive high-budget term on the original L² norm.

`exists_sobolev_commutators_of_matrix_representation` constructs the entire
real commutator family from joint smoothness, chart support and primitive entry
budgets. Its constant is fixed before the amplitudes and their common high
budget. It uses the literal normal representation from `Translation.Assembly`
and discharges the complex matrix and exterior commutator premises.

The normal producer retains instantiation of that representation and its
primitive budgets. The parent inverse construction retains coercivity,
first-order inverse preservation and the quantitative bootstrap assembly.
-/
