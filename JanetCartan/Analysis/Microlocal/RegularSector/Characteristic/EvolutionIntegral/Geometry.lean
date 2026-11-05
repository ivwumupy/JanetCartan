module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Geometry.Differential
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Geometry.Locality
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Geometry.MixedBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Geometry.AveragedGeometry

/-!
# Geometry of the elapsed-time phase

Checked triangular mixed and full-segment averaged-gradient formulas for
`app:ch_regular_base:eq:fixed-time-representation`, mixed determinant and
inverse bounds uniform in elapsed time, and actual supported phase locality.
The locality interface is the existing `SupportedSobolev.IntegerBounds`:
no smoothness at spatial frequency zero is inferred from nonzero spacetime
frequency. Primitive spatial mixed near-identity control also gives uniform
whole-image averaged-Jacobian gaps and injectivity on common buffered domains.
The spatial averaged block follows the full spacetime segment. The parent's
spatial phase supplies the primitive regularity and mixed control; graph
realization and the final retarded analytic assembly remain with the parent.
-/
