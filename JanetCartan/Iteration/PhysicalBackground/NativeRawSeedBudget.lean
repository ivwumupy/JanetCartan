module

public import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSource
public import JanetCartan.Iteration.PhysicalBackground.OriginalReferenceStrong
public import JanetCartan.Iteration.PhysicalBackground.ReferenceBudget
public import JanetCartan.Iteration.PhysicalInverseContinuity.Original
import all JanetCartan.Iteration.PhysicalInverseContinuity.Original
public meta import JanetCartan.Iteration.PhysicalBackground.NativeRawSeedBudgetTemplate

/-!
# Actual PhysicalSeed raw reference half-budget before sigma

Consumer: the SAME current raw input in `NativeDensity`, using its exact
`Original.raw_half` comparison (`app:ch_background:eq:bg-density-input`).
The original21 input here has not yet received the strong cap: apply it ONCE
before task74's weight and `NativeReferenceSource`. The reference row, source,
carrier radius and original exterior are retained. The final source cap lies
inside the native current-normal-inverse interval (ABI slot22) and the
strengthened source/profile interval (slot23). The distinct regular-sector
source cap is NOT compared here; the parent may take a further common minimum.
No history, high-order seminorm or successful raw-smallness assumption is an
input to the choice.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalBackground

/-- Equal actual residual fields produce the same measured source, independently
of their smoothness certificates. This does not change the physical cutoff. -/
theorem nativeReference_measuredSource_congr {n : ℕ} {r : ℝ}
    (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    {Q Q' : Euclidean n → Fin n → MetricTensor n} {R R' : MetricField n}
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hQ' : ContDiffOn ℝ ∞ Q' (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r)))
    (hR' : ContDiffOn ℝ ∞ R' (ball 0 (4 * r)))
    (hq : Q = Q') (hr' : R = R') :
    measuredSourceToL2 hr hcell Q R hQ hR = measuredSourceToL2 hr hcell Q' R' hQ' hR' := by
  subst Q'
  subst R'
  rfl

end JanetCartan.PhysicalBackground
end

realize_native_raw_seed_half_budget
