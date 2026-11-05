module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Rows.Real

/-!
# Unchanged annular sampling rows and prefixes

Checked finite-row deductions for `app:ch_waves:eq:sampling-prefix-normal` and
`app:ch_waves:eq:sampling-operator-bounds`. Every prefix uses the same full
`RawInputRealization.Input`; taking `Finset.univ` recovers `annularRow`.

The parent instantiates the bands with `BandKernelData.operator`. Its Hilbert–
Schmidt and continuity theorems provide those hypotheses. The sharper per-band
squared operator estimate of order `2^i` remains an explicit analytic input
from `jc-raw-primary-slice-l2`. These deductions do not assert that estimate.
-/
