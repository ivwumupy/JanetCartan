module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.DistributionalLimit
public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.WeakConjugation

/-!
# The two-term graph conjugation identity

`TwoTermGraphRegularization.conjugation` proves the exact literal
compact-frequency identity in `app:ch_regular_base:eq:direct-graph-identity`.
It uses the actual normalized adjugate, actual phase Hessian and correction
amplitude derivatives, and the existing transport cancellation. Output
differentiation and canonical-source integration by parts preserve the iterated
Euclidean Lebesgue integrals and the physical `(2π)⁻ⁿ` normalization.

The remaining conditional inputs are the smooth phase and transport matrix,
their eikonal and transport equations, local symbol regularity, and the smooth
compact frequency mask and masked amplitude. The actual producers are
`jc-hamilton-phase`, `jc-compatible-phase-geometry`, and `jc-finite-fio-calculus`;
`jc-finite-fio-calculus` and `jc-regular-sector` must instantiate every input.

`twoTermGraph_distributional_conjugation` proves the unregularized identity on
every compact test supported in the output chart, conditional on convergence of
the three actual undifferentiated graph sequences. Weak output integration by
parts identifies the left side with the physical operator on the two-term graph
limit. Pairing integrability follows from local smoothness and compact support;
no differentiated-limit hypothesis is needed. The local smoothness of the
physical coefficients and the three convergence statements remain inputs of the
finite FIO construction. `twoTermGraph_pairing_limit` retains the simpler
three-pairing limit statement for other consumers. No unconditional existence
of the phase, transport solution, or unregularized limits is asserted.
-/
