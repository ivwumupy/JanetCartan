module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ExtendedSymbol
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.FrameComponents

/-!
# Actual comparison phases for the fixed coefficient extension

This is the comparison-phase construction in `app:ch_regular:thm:no-return`
for the literal extended frame. Both frozen transversality and scalar-symbol
closeness are discharged. The fixed geometry and frame threshold precede the
current frame; no coverage hypothesis is imposed on the source product.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open ActualCarriers ActualCarriers.FrozenPhaseReference HamiltonPhase PhaseCover

/-- Complete source-product comparison charts for the actual affine extension.
The source radius can be prescribed to lie below any fixed positive bound.
Every scalar-symbol and transversality premise of the comparison-chart producer
is derived from primitive frame `C⁶` closeness here
(`app:ch_regular:thm:no-return`, finite comparison-phase paragraph). -/
theorem exists_extended_frame_comparison_cover {n : ℕ} (hn : 5 ≤ n)
    (p : BallExtension.Parameters (Euclidean n)) {R : ℝ} (hR : 0 < R)
    {Ω : Set (Euclidean n)} (hΩ : IsCompact Ω)
    (hbad : Disjoint Ω (cubeBadSubspaceUnion n)) :
    ∃ (s : Finset {ξ : Euclidean n // ξ ∈ Ω ∧ (frozenSymbol n).h (0, ξ) = 0})
      (g : s → ComparisonGeometry (Euclidean n)) (r δ c C ε : ℝ)
      (A : Set (Euclidean n)),
      0 < r ∧ r < R ∧ 0 < δ ∧ 0 < c ∧ 0 < C ∧ 0 < ε ∧
      (∀ i : s, 3 * r < (g i).radius) ∧ IsCompact A ∧
      A ⊆ (cubeBadSubspaceUnion n)ᶜ ∧
      (∀ q ∈ A, closedBall q ε ⊆ (cubeBadSubspaceUnion n)ᶜ) ∧
      ∀ (Q : Euclidean n → Fin n → MetricTensor n)
        (hQ : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞ Q x),
        cNorm (closedBall p.center p.radius) 6 (Q - fun _ ↦ cubeStress n) < δ →
        let H := normalizedHomogeneousSymbol isOpen_univ (affineFrameExtension p Q)
          (contDiff_affineFrameExtension p
            (fun x hx ↦ (hQ x hx).contDiffWithinAt)).contDiffOn;
        ∃ charts : (i : s) → ComparisonChart H (g i),
          (∀ η : ComparisonGeometry.ParameterFamily g,
            ∀ x ∈ closedBall 0 (2 * r),
            c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
              ‖ComparisonChart.familyGradient charts η x‖ ≤ C ∧
              normalizedCovector (ComparisonChart.familyGradient charts η x) ∈ A) ∧
          ∀ x ∈ closedBall 0 r, ∀ ξ ∈ Ω, H.h (x, ξ) = 0 →
            ∃ η : ComparisonGeometry.ParameterFamily g,
              ξ = ComparisonChart.familyGradient charts η x := by
  obtain ⟨s, g, r₀, d, c, C, ε, K, A, hr₀, hd, hc, hC, hε,
    hK, hKD, _hsource, hri, hA, hAbad, hAbuffer, hcover⟩ :=
    exists_cube_comparison_cover hn hΩ hbad
  obtain ⟨δ, hδ, hsmall⟩ := exists_extended_symbol_comparison_radius p hK
    (fun z hz ↦ (mem_frozenSymbol_domain z).mp (hKD hz)) 3 hd
  let r := min r₀ R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrr₀ : r ≤ r₀ := by
    have := min_le_left r₀ R
    dsimp [r]
    linarith
  have hrr : r < R := by
    have := min_le_right r₀ R
    dsimp [r]
    linarith
  refine ⟨s, g, r, δ, c, C, ε, A, hr, hrr, hδ, hc, hC, hε,
    fun i ↦ lt_of_le_of_lt (by linarith) (hri i), hA, hAbad, hAbuffer, ?_⟩
  intro Q hQ hlow
  let hE := contDiff_affineFrameExtension p (fun x hx ↦ (hQ x hx).contDiffWithinAt)
  let H := normalizedHomogeneousSymbol isOpen_univ (affineFrameExtension p Q) hE.contDiffOn
  have hD : (frozenSymbol n).domain ⊆ H.domain := Subset.rfl
  have hs : cNorm K 3 (fun z ↦ H.h z - (frozenSymbol n).h z) ≤ d :=
    (hsmall Q hQ ((cNorm_mono_order (by decide : 3 ≤ 6)).trans_lt hlow)).le
  obtain ⟨charts, hb, hv⟩ := hcover H hD
    (contDiffOn_normalizedSymbol isOpen_univ hE.contDiffOn)
    (normalizedHomogeneousSymbol_conic isOpen_univ _ hE.contDiffOn) hs
  exact ⟨charts,
    fun η x hx ↦ hb η x (closedBall_subset_closedBall (by linarith) hx),
    fun x hx ξ hξ hz ↦ hv x (closedBall_subset_closedBall hrr₀ hx) ξ hξ hz⟩

/-- Smoothness of the literal projected frame on the coefficient ball follows
from the current immersion and its full normal rank. This is the concrete
analytic input to `exists_extended_frame_comparison_cover`
(`app:ch_seed:setup:seed-current`, `app:ch_regular:thm:no-return`). -/
theorem projectedStress_contDiffAt_on_ball {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n))
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hball : closedBall p.center p.radius ⊆ U)
    {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F U)
    (himm : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U) :
    ∀ x ∈ closedBall p.center p.radius,
      ContDiffAt ℝ ∞ (ProjectedStressFrame.projectedStress F) x := by
  intro x hx
  apply contDiffAt_pi.mpr
  intro i
  exact (ProjectedStressFrame.contDiffOn_projectedStress hU hF himm hrank i).contDiffAt
    (hU.mem_nhds (hball hx))

/-- A positive componentwise current-frame neighborhood supplies any prescribed
joint `C⁶` neighborhood of the literal projected frame. In particular it
instantiates the threshold returned by `exists_extended_frame_comparison_cover`
without assuming a symbol or phase estimate (`app:ch_regular:thm:no-return`). -/
theorem projectedStress_cNorm_lt_of_componentwise {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n))
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hball : closedBall p.center p.radius ⊆ U)
    {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F U)
    (himm : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {δ : ℝ} (hδ : 0 < δ)
    (hsmall : ∀ i, cNorm (closedBall p.center p.radius) 6
      (fun x ↦ ProjectedStressFrame.projectedStress F x i - cubeStress n i) < δ / 14) :
    cNorm (closedBall p.center p.radius) 6
      (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < δ := by
  apply CurrentFullPhase.frame_cNorm_lt_of_componentwise (isCompact_closedBall _ _)
    (fun x hx ↦ ((projectedStress_contDiffAt_on_ball p hU hball hF himm hrank x hx).sub
      contDiffAt_const).of_le (by simp)) hδ
  norm_num only at ⊢
  exact hsmall

end JanetCartan.ProtectedFlow
