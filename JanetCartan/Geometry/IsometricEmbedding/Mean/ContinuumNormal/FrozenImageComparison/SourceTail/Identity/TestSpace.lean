module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.Factorization

/-!
# Compact tests inside the auxiliary plateau

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, the auxiliary physical
cutoff is one on a neighborhood of the closed input ball. Compact smooth tests
inside this open plateau permit removal of the auxiliary cutoff even after
differentiation. Their L² closure must contain the supported inputs before
the test energy identity can be applied to arbitrary supported L² data.
Consumer: `fixedEuclideanChannel_energy_defect_eq_kernel`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff
open JanetCartan.PeriodicLocalL2 JanetCartan.ContinuumRow

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R²" => EuclideanL2 n E

/-- Real L² representatives of compact smooth tests supported strictly inside
the auxiliary plateau. This set specifies only test regularity and support;
the source-tail energy identity is a separate proof obligation
(`app:ch_background:prop:bg-frame`). -/
def fixedSourceTailTestInputs (hR : 0 < R) : Set R² :=
  {u | ∃ g : E → E, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
    tsupport g ⊆ interior {x | FixedCutoffs.physical hR 0 x = 1} ∧
    u =ᵐ[volume] g}

/-- The test support region contains a neighborhood of the entire closed
input ball, as required by compact mollification in the source-tail density
argument (`app:ch_background:prop:bg-frame`). -/
theorem closedBall_subset_fixedSourceTailTest_plateau (hR : 0 < R) :
    closedBall (0 : E) R ⊆ interior {x | FixedCutoffs.physical hR 0 x = 1} := by
  simpa using FixedCutoffs.physical_plateau (n := n) hR 0

end JanetCartan.ContinuumNormal.FrozenImageComparison
