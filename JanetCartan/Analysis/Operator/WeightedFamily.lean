module

public import JanetCartan.Analysis.Operator.WeightedFamily.Synthesis
public import JanetCartan.Analysis.Operator.WeightedFamily.Rows

/-!
# Finite weighted family estimates

Reusable finite Cauchy–Schwarz and norm estimates for `main:eq:primary-strain`,
`app:ch_mean_pairs:eq:mean-canonical-weighted-low`, and
`app:ch_pairs:eq:pairs-weighted-U` in `paper.tex`.

`WeightedFamily.Scalar` proves the primary coefficient bound and the exact ordered
pair and off-diagonal coefficient identities. `WeightedFamily.Synthesis` assembles
vectors in any real normed space. `WeightedFamily.Rows` preserves the literal
coefficient of squared raw estimates and identifies the weighted energy with an
`ℓ²` norm. All allow zero weights and empty finite families.

These are finite-family estimates, not proofs of the analytic input theorems:
individual wave bounds, the canonical row identity and its uniform operator bound
remain inputs in applications. No estimate introduces an extra sample-count factor.
-/
