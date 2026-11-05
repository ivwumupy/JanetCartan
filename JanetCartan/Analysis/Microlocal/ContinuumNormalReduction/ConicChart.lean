module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ConicChart.Smooth
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ConicChart.Transport

/-!
# Conic extension of the transport annular inverse

Checked conditional deductions for `app:ch_background:prop:bg-frame`, Step 1:

* Transverse comparison and the strict buffers `r₋(1 + δ) < 1 < r₊(1 - δ)`
  simultaneously normalize equal outputs into the injective annular chart.
* The annular inverse extends to the cone, independently of normalization.
  Its incidence component has degree zero and its covector component degree one.
* Joint smoothness follows from the joint annular inverse; the required
  normalized-image containment is proved, not assumed, in
  `inverse_family_contDiffOn_of_annular`.
* The actual averaged gradient of `Y(x,s,v) · η` is homogeneous. Differentiating
  this identity with `s` fixed proves the degree-one absolute Jacobian and
  `c|η| ≤ J ≤ C|η|`. The output norm is comparable to `|η|`, including in the
  physical Hilbert norm. Compactness supplies annular upper bounds.

The analytic inputs remain conditional: the actual smooth `Y`, compact support
containments, annular injectivity, transverse comparison with `0 ≤ δ < 1`,
positive annular determinant gaps, and a joint smooth annular inverse branch.
Their producers are `jc-full-phase-charts` and `jc-normal-inverse-coefficients`.
The consumers `jc-continuum-normal-reduction` and `jc-continuum-row` must instantiate
these inputs; this module does not assert the unconditional continuum theorem.

All spaces retain their real Hilbert/Euclidean interpretation. No input measure
or torus identification is introduced here.
-/
