module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.GlobalConstruction

/-!
# Global carrier normal realization

Checked construction for `app:ch_background:prop:bg-frame`, Step 1:

* the original full reflected amplitude in the exact paired PDO coordinates,
  retaining both measurement supports and the normalization `k = 2πξ`;
* a compact parameter-mask construction compatible with the original radial
  symbol: its kernel, operator action and adjoint are proved unchanged;
* global equality of the actual finite real normal and the transferred full
  matrix PDO, including the output-chart indicator and both measure transports;
* the full-amplitude derivative budget and uniform finite real and complex
  normal bounds from primitive finite norms, retaining one high budget;
* the unique uncut complex carrier extension, literal test L² membership,
  operator and adjoint norm bounds, and output support on all input L² data;
* literal uncut adjoint L² membership and identification for that SAME extension,
  and strong convergence of the actual finite adjoints;
* equality of that extension's real normal with the GLOBAL transferred full
  matrix PDO on all output L² data, by the two finite-normal limits and density.

`exists_carrierL2Extension_globalNormal_of_primitiveNorms` in the namespace
`CarrierNormalRealization` supplies all these analytic constructions without
assuming an operator bound, uncut adjoint membership, source integrability,
distributional limit or normal identity. The constants precede the varying
fields, high budget and radial cutoff radii. Choosing its entry reserve
`s = 2 * (n + 1) + 1`, with geometry order `s + 2`, supplies the carrier part of
`ContinuumCommutator.Translation.Assembly` and the differential commutator.
The reflected symbol already includes the factor four: its coefficient in
that representation is one.

The actual geometric-family and coefficient/chart matching, image-channel
normal assembly, exterior algebra and coercivity remain parent obligations.
-/
