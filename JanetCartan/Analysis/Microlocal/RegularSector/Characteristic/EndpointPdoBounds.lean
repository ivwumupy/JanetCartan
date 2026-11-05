module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.Masks
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.IntegerBounds

/-!
# Source and upper-endpoint PDO budgets

For `paper-v2.tex`, `app:ch_regular_base:eq:energy-complete-residual`:

* `exists_finiteMask_source_pdo_budgets` proves joint smoothness, fixed
  paired-position support, every order-zero position budget and the
  `GraphNormalAmplitudeBounds` input for the literal conic source symbol.
* `exists_supported_endpoint_pdo_budgets` proves those properties and the
  full-frequency weighted position budgets for the literal supported
  `W₁ = curryCharacteristicMatrix (collared ℓ 1 angular
  (bufferedMatrix V κ (pencilAmplitudeFamily ... 1)))`.
* `exists_endpoint_integer_gain_constants` applies the existing matrix PDO
  estimates to the SAME endpoint and its literal Hilbert adjoint, with one
  original coefficient reserve `2 * (d + 2) + 11`.

The amplitude input is precisely the published joint normalized output of
`UniformAmplitudes.exists_uniform_supported_conic_pencilAmplitudes`, with
reserve ten in original `Q` and nine in `B`. Both time slots are differentiated
on the diagonal. The matrix product uses the existing single-high tame
product theorem. The frequency conversion remains `ξ_phys = 2π ξ`, and the
right multiplier's cone proves full-frequency order minus one.

The parent instantiates the physical image inclusion and the explicit
normalized support criterion `diagonal_shell_cover_of_radial_support` on
its SAME finite family. These are geometric obligations, separate from the
proved conditional symbol estimates. No PDO coordinate derivative budget,
bounded endpoint operator, or replacement amplitude is an input. This file
does not assert the complete sector solver or the unconditional embedding.
-/
