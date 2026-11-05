module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.CurrentNeighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.FullCoefficientDilation.Bounds

/-!
# Reference margins on a common source-scale interval

Supply the sole reference-margin premise of `exists_primitive_signed_no_return`
from the actual source-dilation bounds. The interval precedes the source scale,
so the shared initialization can choose its one scale inside this cap while
retaining the same reference for target normalization and history smoothing.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open ProjectedStressFrame ReferenceInitialization.FullCoefficientDilation

/-- Every sufficiently small positive source scale supplies the prescribed
finite-order reference margin (`app:ch_regular:thm:no-return`, `main:prop:seed`).
This is an interval statement, so it persists when the common initialization
shrinks the source scale to satisfy its other fixed margins. -/
theorem exists_source_dilation_protected_reference_margin {n : ℕ}
    (G₀ : FlatReference n) {b η : ℝ} (m : ℕ) (hη : 0 < η) :
    ∃ cap > (0 : ℝ), cap ≤ 1 ∧ ∀ σ ∈ Ioc (0 : ℝ) cap, ∀ i,
      cNorm (closedBall (0 : Euclidean n) b) m
        (fun x ↦ projectedStress (sourceDilation G₀.map σ) x i - cubeStress n i) < η := by
  obtain ⟨U, _hU, _hKU, σ₀, hσ₀, hσ₁, _hseg, _hgeom, hbound⟩ :=
    exists_fullReducedCoefficients_dilation_bounds G₀
      (isCompact_closedBall (0 : Euclidean n) b)
  obtain ⟨C, hC, hb⟩ := hbound m
  let cap := min σ₀ (η / (2 * C))
  have hcap : 0 < cap := lt_min hσ₀ (div_pos hη (by positivity))
  refine ⟨cap, hcap, (min_le_left _ _).trans hσ₁, ?_⟩
  intro σ hσ i
  have hs : σ ∈ Ioc (0 : ℝ) σ₀ := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hc := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp
    (hσ.2.trans (min_le_right _ _))
  exact ((hb σ hs).2 i).trans_lt (by nlinarith)

end JanetCartan.ProtectedFlow
