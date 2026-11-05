module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.FiniteJets
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.PrimitiveNormalData

/-!
# Exact differentiated raw slice amplitudes

For `app:ch_waves:eq:individual-raw-slice`, the modules here prove:

* the all-order mixed derivative expansion of the literal original wide-band
  integral, with one unchanged phase and exact frequency powers `κ^q`;
* the branch joint-jet estimate with excess `s-q+k-R` and the fixed manuscript
  reserve `Dpr+r_par+2`, where `M=20(n+1)` and `r_par=M+3`;
* the additional parameter derivative, normalization by `L^(s-q)`, support
  containment, and the resulting SingleChannel primitive input;
* original-chart producers for the joint grades, using the literal shifted
  covector and the smooth integral extension of the quotient at epsilon zero;
* exact identification of the joint branches with physical band branches,
  including time derivatives taken before restriction to a spatial slice;
* uniformity over the original rescaled masks with a common primitive mask
  profile, and the bounded finite-jet specialization at `L=1`.

The main constructor is `exists_rawSlicePrimitiveBranchNormalData`. Its analytic
inputs are primitive original amplitude and covector-differential jets through
`s+M+1`, original fixed-mask jets through that order, and the unchanged phase
geometry. Every differentiated amplitude input field is derived. The covector
differential uses original phase jets through `s+M+2`. If the coefficient
producer has the common fixed shift `Dpr`, the sufficient coefficient and
initial-data order is `s+M+2+Dpr`; the producer must actually certify that shift.

The parent `jc-raw-differentiated-slice-assembly` retains actual WKB/history
instantiation of these explicit original-chart premises, weak-integral
realization, coordinate transfer, and final Sobolev assembly. This module
constructs the differentiated primitive input, not an unconditional raw family.
-/
