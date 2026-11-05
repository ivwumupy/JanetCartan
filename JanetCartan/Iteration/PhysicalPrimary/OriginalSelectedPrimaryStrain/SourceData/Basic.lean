module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalPrimaryStrainMaskData

/-! # The original finite-history map in the primary tensor admission

The source in `main:eq:primary-strain` uses the fixed flat reference plus its
finite Schwartz history. Its smoothness is a consequence of those data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open scoped ContDiff

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData

/-- Smoothness of the identical original finite-history map on its source
chart, prior to taking the full tensor strain. -/
theorem finite_reference_smooth {n j : ℕ} (G : FlatReference n)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
    (U : Set (Euclidean n)) :
    ContDiffOn ℝ ∞ (RevisedGlobal.finiteMap G.map u) U :=
  RevisedGlobal.contDiffOn_finiteMap G.contDiff.contDiffOn u

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
end
