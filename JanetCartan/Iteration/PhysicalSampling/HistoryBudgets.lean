module

public import JanetCartan.Iteration.PhysicalHistory
public import JanetCartan.Iteration.PhysicalGeometry.Neighborhood

/-!
# Actual physical-history budgets for the scalar auxiliary row

The scalar continuation in `OnWorkingRadius` needs a fixed map bound at order
`20 * (n + 1) + 5`, the metric gap, and the current normal-space gap. They follow
from the actual Schwartz history and the fixed reference BEFORE any current
map. No density amplitude, inverse response, torus history, or analytic bound
is assumed. The low-six cube tolerance is supplied separately by the SAME
original source/current producer in `OriginalPhaseMargins`
(`main:eq:history-current`, `app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalSampling
open RevisedConvergence GeometricProfile ProjectedStressFrame

/-- The exact high fixed scalar map norm and geometric gaps are consequences
of admissible physical Schwartz histories. All constants precede every history;
the only reserve condition is the actual order used by the scalar factory. -/
theorem exists_scalar_physical_history_budgets {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {B : ℝ} (hB : 1 ≤ B) {rStar kMin : ℕ}
    (hreserve : 20 * (n + 1) + 5 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ M > (0 : ℝ), ∃ κ > (0 : ℝ),
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      ContDiffOn ℝ ∞ F (ball 0 R) ∧ IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
      cNorm (closedBall 0 r) (20 * (n + 1) + 5) F ≤ M ∧
      (∀ x ∈ closedBall 0 r, ∀ v, (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
      ∀ x ∈ closedBall 0 r, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖ := by
  obtain ⟨S, hS, _, _, κ, hκ, hgeometry⟩ :=
    PhysicalGeometry.exists_geometric_neighborhood G hr hrR hR hB
      (by omega : 8 ≤ rStar) horder zero_lt_one
  obtain ⟨A, hA, hprofile⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (isCompact_closedBall (0 : Euclidean n) r) (fun _ _ ↦ G.contDiff.contDiffAt) hB horder
  refine ⟨S, hS, A (20 * (n + 1) + 5) + 1, by linarith [hA (20 * (n + 1) + 5)],
    κ, hκ, ?_⟩
  intro R₀ hR₀ j u ell hu F
  have hsmooth : ContDiff ℝ ∞ F :=
    G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  obtain ⟨hi, hrank, _, hmetric, hnormal, _, _⟩ := hgeometry R₀ hR₀ j u ell hu
  have hp := hprofile R₀ (hS.trans hR₀) j u ell hu _ Subset.rfl (20 * (n + 1) + 5)
  have hmap : cNorm (closedBall 0 r) (20 * (n + 1) + 5) F ≤ A (20 * (n + 1) + 5) := by
    simpa only [Nat.sub_eq_zero_of_le hreserve, pow_zero, mul_one] using hp
  exact ⟨hsmooth.contDiffOn, hi, hrank, hmap.trans (le_add_of_nonneg_right zero_le_one),
    fun x hx ↦ hmetric x (closedBall_subset_ball hrR hx),
    fun x hx ↦ hnormal x (closedBall_subset_ball hrR hx)⟩

end JanetCartan.PhysicalSampling
