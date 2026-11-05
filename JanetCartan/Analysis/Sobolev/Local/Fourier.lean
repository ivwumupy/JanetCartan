module

public import JanetCartan.Analysis.Sobolev.Local.Fourier.RealOrderOne
public import JanetCartan.Analysis.Sobolev.Local.Fourier.RealInteger

/-!
# Euclidean Fourier regularity and genuine restriction Sobolev spaces

The natural-order norm conversion in `app:not:fourier` and
`app:ch_regular_base:eq:sector-theorem-residual`, including an independent
order-one endpoint used by the fixed-inverse contraction in
`app:ch_regular:thm:exact-correction`.

`exists_vector_weakJet_nat` constructs genuine real weak Fréchet jets of
complex vector-valued Euclidean L² data from Fourier H^s membership alone.
`exists_vector_sobolevExtension_nat` and `vector_restrictionSobolev_nat_bounds`
give the corresponding extension and restriction estimates at every natural
order. The constant is independent of the datum and the restriction set;
the explicit bound is `((r + 1) * (1 + 2 * π * n)) ^ s`. The real-fiber
versions use the existing literal L² inclusion and real-part maps, retaining
the same constant and the chosen representative. No smoothness or membership
above the requested order is assumed. The `_one` theorems are available from
the independent `Fourier.OrderOne` and `Fourier.RealOrderOne` leaves.

These conversions do not construct the sector residual or its Fourier bound.
Those analytic inputs must be instantiated by the parent operator construction.
-/
