module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity
public import JanetCartan.Analysis.ContDiff.PositiveSquareRoot

/-!
# Small density corrections give permitted frozen initial amplitudes

The sufficiently small `C^{k_gap}` neighborhood in
`app:ch_background:prop:bg-frame` may be restricted to norm at most `1/2`.
Its zeroth-order term bounds `|v|`, hence `sqrt (1 + v) ≥ 1/2`.
We supply both initial-data hypotheses of the frozen multiplier comparison:
smoothness on the initial domain and the lower bound at the retained labels.
The flow's range and initial-section containment are the same as those used
for integrability, and still must be instantiated by the parent construction.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.ContinuumNormal.FrozenModel
open FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic

/-- The original finite-order smallness hypothesis gives a smooth square-root
initial amplitude and a quantitative lower bound. Consumer:
`frozenInitial_sqrt_admissible_of_cNorm`; source:
`app:ch_background:prop:bg-frame`, change of the initial amplitude. -/
theorem frozenInitial_sqrt_properties_of_cNorm {n : ℕ}
    {v : Euclidean (n - 1) × Euclidean 3 → ℝ}
    {K D : Set (Euclidean (n - 1) × Euclidean 3)}
    (hK : IsCompact K) (hDK : D ⊆ K)
    (hv : ∀ q ∈ K, ContDiffAt ℝ ∞ v q) (kGap : ℕ)
    (hsmall : cNorm K kGap v ≤ 1 / 2) :
    ContDiffOn ℝ ∞ (fun q ↦ Real.sqrt (1 + v q)) D ∧
      ∀ q ∈ K, (1 / 2 : ℝ) ≤ Real.sqrt (1 + v q) := by
  have habs (q) (hq : q ∈ K) : |v q| ≤ 1 / 2 := by
    have h := (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun p hp ↦ (hv p hp).of_le (by simp)) hq (Nat.zero_le kGap)).trans hsmall
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h
  have hpos (q) (hq : q ∈ K) : 0 < 1 + v q := by
    have hl := (abs_le.mp (habs q hq)).1
    linarith
  refine ⟨fun q hq ↦ ?_, fun q hq ↦ ?_⟩
  · exact ((contDiffAt_const.add (hv q (hDK hq))).sqrt (hpos q (hDK hq)).ne').contDiffWithinAt
  · apply Real.le_sqrt_of_sq_le
    have hl := (abs_le.mp (habs q hq)).1
    nlinarith

/-- `sqrt (1 + v)` supplies exactly the smooth-initial-data and retained-label
lower-bound inputs of `canonicalFrozenCarrierSymbol_initial_quadratic_ge_unit`.
The same statement applies to each member of the finite matrix family. Only
the primitive `C^{k_gap}` smallness and the existing flow range/section inputs
are used (`app:ch_background:prop:bg-frame`). -/
theorem frozenInitial_sqrt_admissible_of_cNorm {n : ℕ}
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {v : Euclidean (n - 1) × Euclidean 3 → ℝ}
    {K D : Set (Euclidean (n - 1) × Euclidean 3)}
    {Dflow : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    {z₀ : Euclidean 3} {r a : ℝ} (ha : 0 < a) (har : 6 * a ≤ 3 * r)
    (hK : IsCompact K) (hDK : D ⊆ K)
    (hv : ∀ q ∈ K, ContDiffAt ℝ ∞ v q) (kGap : ℕ)
    (hsmall : cNorm K kGap v ≤ 1 / 2)
    (hseed : MapsTo (fun z : CarrierParameter ↦ ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter z)))
      (ball (z₀ 0) r ×ˢ ball (spectatorCenter z₀) (6 * a)) Dflow)
    (hYrange : MapsTo Y Dflow D) :
    ContDiffOn ℝ ∞ (fun q ↦ Real.sqrt (1 + v q)) D ∧
      ∀ z ∈ carrierSupport z₀ (r := a),
        (1 / 2 : ℝ) ≤ Real.sqrt (1 + v (Y (0, (0, parameter z)))) := by
  obtain ⟨hsmooth, hlower⟩ := frozenInitial_sqrt_properties_of_cNorm hK hDK hv kGap hsmall
  refine ⟨hsmooth, fun z hz ↦ hlower _ (hDK (hYrange (hseed ?_)))⟩
  exact ⟨closedBall_subset_ball (by linarith) hz.1,
    closedBall_subset_ball (by linarith) hz.2⟩

end JanetCartan.ContinuumNormal.FrozenModel
