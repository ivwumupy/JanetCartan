module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedGeometry
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedStationaryTemplate

/-!
# The original signed critical branches on the native mask window

The original current construction supplies all FOUR independent source-sign /
literal-adjoint critical branches. Restrict their certificates to the original
mask window; do not choose a new critical point, change the phase, or shorten
the actual operator interval `[0,3*maskRadius/4]`. The complete pointwise package
(invertible averaged Hessians, phase value zero and all retained segments) is
preserved verbatim.

Consumer: the actual original-data application of the whole-source retarded
constructors and `exists_physical_history_measured_residual_hstep`
(`app:ch_response:eq:fixed-factor-transfer`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16000
open Set Metric
open scoped ContDiff
namespace JanetCartan.PhysicalPrimary.OriginalRetardedStationary

/-- Restrict only the domain of the already constructed critical branch. The
pointwise proposition is the entire original critical/Hessian/segment package;
its function and all constants are unchanged. -/
theorem restrict_stationary_to_mask {d : ℕ} {r τ : ℝ} (hτ : r ≤ τ)
    {U : Set (Euclidean (d+1) × (Euclidean 3 × Euclidean d))}
    {D : Set (WithLp 2 (Euclidean (d+1) × Euclidean (d+1)))}
    (Ψ : (ℝ × (Euclidean (d+1) × (Euclidean 3 × Euclidean d))) ×
      WithLp 2 (Euclidean (d+1) × Euclidean (d+1)) → ℝ)
    (κ : ℝ × (Euclidean (d+1) × (Euclidean 3 × Euclidean d)) →
      WithLp 2 (Euclidean (d+1) × Euclidean (d+1)))
    (P : ℝ × (Euclidean (d+1) × (Euclidean 3 × Euclidean d)) → Prop)
    (hΨ : ContDiffOn ℝ ∞ Ψ ((Ioo (-2*τ) (2*τ) ×ˢ U) ×ˢ D))
    (hκ : ContDiffOn ℝ ∞ κ (Ioo (-2*τ) (2*τ) ×ˢ U))
    (hP : ∀ q ∈ Ioo (-2*τ) (2*τ) ×ˢ U, P q) :
    ContDiffOn ℝ ∞ Ψ ((Ioo (-2*r) (2*r) ×ˢ U) ×ˢ D) ∧
      ContDiffOn ℝ ∞ κ (Ioo (-2*r) (2*r) ×ˢ U) ∧
      ∀ q ∈ Ioo (-2*r) (2*r) ×ˢ U, P q := by
  have ht : Ioo (-2*r) (2*r) ⊆ Ioo (-2*τ) (2*τ) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hsub := Set.prod_mono ht (subset_rfl : U ⊆ U)
  exact ⟨hΨ.mono (Set.prod_mono hsub subset_rfl), hκ.mono hsub,
    fun q hq ↦ hP q (hsub hq)⟩

retain_original_mask_window_stationary

end JanetCartan.PhysicalPrimary.OriginalRetardedStationary
