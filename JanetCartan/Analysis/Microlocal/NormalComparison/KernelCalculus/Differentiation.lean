module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Differentiation.Normal
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Oscillatory

/-!
# Operator norm parameter differentiation of compact kernels

For Step 2 of `app:ch_osc:prop:osc-normal`, this module proves:

* a quantitative operator norm bound on fixed compact spatial supports;
* continuity and compact support of the actual parameter derivative;
* operator norm differentiation of the constructed scalar and finite vector
  integral operators from joint C¹ regularity and fixed compact support;
* the product rule for their actual masked normal composition and Hilbert adjoint.

The input domain may have infinite measure. The mask is a fixed L∞ element;
no mask differentiability is required for these results. Frequency may be fixed,
so no uniform frequency bound is asserted by this differentiation argument.
-/
