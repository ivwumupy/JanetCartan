module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RootFamily.Quantitative

/-!
# Uniform actual roots of nearby stress pencils

`RootFamily.exists_coordinateSplit_uniform_fieldRoot` constructs one
coefficient-parameter branch from a fixed regular frozen pencil. It selects
one `coordinateSplit i` using the frozen transverse derivative. The original
adjugate entry is an input of the frozen data and is retained throughout the
family. `exists_uniform_fieldRoot` also exposes the geometric construction
in an already selected transverse coordinate system.

For `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel`, the coefficient neighborhood,
physical/conic domain, normalized compact buffers, scalar band, root range,
and positive minor/transport gaps all precede the variable smooth field `Q`.
The same branch solves each field's actual characteristic equation and extends
homogeneously on every positive ray. Normalized gaps and their actual radial
powers are distinguished explicitly.

The joint `cNorm` bounds use the original `Q` on the prescribed physical
ball, with zero derivative loss and a single high norm. Their constants and
the nested state buffers precede `Q`; finite-low and graded bounds follow
for the same branch. Actual compact-state minor/transport gaps retain the
radial factors explicitly. The consumers are the actual two-time flow family
and the primitive amplitude and evolution symbol budgets. Finite sector
covering and the production of history coefficient bounds belong to the
parent constructions.
-/
