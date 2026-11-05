module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.WeakDerivative.Iterated

/-!
# Weak coordinate derivatives on the periodic Sobolev scale

Distributional derivatives for the integer induction in
`app:ch_background:prop:bg-inverse`, tested against all smooth periodic fields.

* Weak coordinate derivatives are unique and agree with classical derivatives.
* Smooth density and completeness construct bounded derivative maps
  `H^(s+1) → H^s` with norm at most one and the physical `2π` Fourier symbol.
* Membership in `H^(s+1)` is equivalent to membership in `H^s` together with
  coordinate weak derivatives in `H^s`.
* Iterated distributional derivatives are defined directly by integration
  against differentiated tests. Their L² representability through order `s`
  characterizes `H^s`, with an explicit top-order integer induction step.

All statements preserve zero-dimensional tori and finite-dimensional real
Hilbert codomains. The underlying norm is the actual Fourier Sobolev norm.
-/
