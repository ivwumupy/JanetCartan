module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.Comparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.RawReferenceBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.SmoothRealization
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.ComponentOperator
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.SharpBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.IndividualBounds

/-!
# Canonical changes for a fixed current row

For `main:prop:canonical` and `app:ch_mean_pairs:defn:mean-canonical`, the
imported comparison lemmas transfer a complete normal comparison and raw
estimates to canonical adjoint bounds, including the continuum inverse.
The smooth realization applies the SAME component adjoints and inverse to
the supplied raw derivative maps, and proves their exact weighted cross
response with the unchanged zero-atom background.
The component operator itself is constructed from that smooth raw response:
its continuity and operator bound follow from the raw derivative's L² bound.
The same operator's complete residual then agrees with the L² recurrence
without a separate raw-response identification premise.
The reference-normal bound is derived from contractivity of the original
raw masks and the norm of the SAME uncut augmented row.
Positivity of the original cut auxiliary normal is proved. For the constructed
component maps, primitive raw estimates and the same normal comparison imply
sharp weighted and accumulated `C^s` and `H^s` bounds, retaining the original
inverse norm and the sum of source residual norms.
The individual component norm now follows from the SAME raw `H^0` bound,
giving individual `K^(s+(n+1)/2)` updates and finite accumulation without
dividing by sample weights. Adding the original prepared base yields its
full individual profile once the proved residual budget is applied.

This is partial progress: the actual corrected atomic maps, original uncut
zero-atom background, and their initial-variable Fourier support and estimates
must still be supplied by the RawPrimary, CorrectedAtoms, background, inverse,
and simultaneous-sampling constructions. No instance of the full source
proposition is asserted here.
-/
