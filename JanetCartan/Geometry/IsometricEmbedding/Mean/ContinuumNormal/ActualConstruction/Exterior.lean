module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.InnerCutoff

/-!
# Identification of the retained inner exterior cutoff

The frozen construction's `innerCutoff` is literally the standard exterior
cutoff at half its support radius. This identifies the SAME function for
`CoerciveNormal.rightInverse_physicalRow_on_core` and the normalized-source
inverse, retaining its squared complement and every outer measurement mask.
Source: `app:ch_background:defn:bg-row`, `app:ch_background:eq:bg-global-bound`.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumNormal.ActualConstruction

open ContinuumRow

/-- The small-support cutoff is the standard exterior-complement cutoff at
the existing core radius `r / 2`; this is equality of the constructed functions,
not a new choice of masks (`app:ch_background:defn:bg-row`). -/
theorem innerCutoff_eq_fixed_core {n : ℕ} {r : ℝ} (hr : 0 < r)
    (hcell : r < 1 / 2) (hcorecell : 4 * (r / 2) < 1 / 2) :
    innerCutoff (n := n) hr hcell = FixedCutoffs.periodic (half_pos hr) hcorecell 0 := by
  have hphysical : innerPhysicalCutoff (n := n) hr = FixedCutoffs.physical (half_pos hr) 0 := by
    simp [innerPhysicalCutoff, FixedCutoffs.physical, show (2 : ℝ) * (r / 2) = r by ring]
  ext z
  simp only [innerCutoff_apply, FixedCutoffs.periodic_apply, hphysical]

end JanetCartan.ContinuumNormal.ActualConstruction
