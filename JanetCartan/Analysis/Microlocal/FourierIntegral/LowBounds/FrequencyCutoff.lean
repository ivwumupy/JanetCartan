module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.OperatorLimit

/-!
# Frequency regularization for the low graph bound

The actual smooth physical-frequency cutoffs for
`app:ch_regular_base:thm:actual-calculus`, Step 1, together with their
self-adjoint contractive multipliers on vector Lebesgue L², Schwartz
preservation, and literal graph convergence on Schwartz and compact smooth
inputs. The L² graph dominator is derived from Schwartz Fourier moments
and fixed compact output support.

`compactVectorGraph_cut_eq_comp` identifies the actual regularizations with
`T.comp P_j` if a bounded `T` realizes the uncut graph on Schwartz inputs.
Both the graphs and their literal Hilbert adjoints then converge strongly.
Construction and realization of that uncut bounded `T` remain the obligation
of the consuming source-independent low-bound theorem.
-/
