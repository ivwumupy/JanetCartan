module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Factorization
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.OrderedDerivatives
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Normal
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.TameEstimates

/-!
# Differential factors of the actual image normal

Checked prerequisites for the image contribution to
`app:ch_background:eq:bg-commutator`:

* the exact finite factorization of the published image channel and its
  literal Hilbert-adjoint normal, with both masks and all coefficient terms;
* constructed Sobolev actions of the constant `J` and `Dᵢ J` factors;
* their contraction bounds, physical `2π` symbols, and actual adjoints;
* commutation of those actions with the existing ordered Sobolev derivatives.

The coefficient Leibniz expansion is constructed in `Normal.lean`, with the
exact weak identity and `K` supplied by `exists_imageNormal_commutators`.
`WeightedEstimates.lean` proves the primitive branch bounds from the first-jet
baseline and weighted Sobolev interpolation. `TameEstimates.lean` completes the
single-high estimate with both masks fixed before the constants. Its endpoint
`exists_imageNormal_tame_commutators` supplies the exact `K/hK` and tame bound,
with fixed coefficient low order one and geometric reserve two. The parent
must instantiate the primitive coefficient budgets on its same row.
-/
