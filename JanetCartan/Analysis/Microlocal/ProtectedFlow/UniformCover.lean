module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ExtendedPhaseCover
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover.UniformWeights

/-!
# Uniform rectangles for the literal extended frame

Discharge the symbol and frozen transversality inputs of the uniform phase-cover
producer for `app:ch_regular:thm:no-return`. The same fixed affine extension is
used throughout. The finite centers and all four weights precede the frame.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open ActualCarriers ActualCarriers.FrozenPhaseReference HamiltonPhase PhaseCover
open FiniteChain.Retarded

/-- Complete-product comparison charts, fixed rectangles and four fixed weights
for the actual extended frame (`app:ch_regular:thm:no-return`). Every smallness
input to the Hamilton producer follows from primitive frame closeness. The time
cap is prescribed after the source radius, before the current frame. -/
theorem exists_extended_frame_uniform_cover {n : ℕ} (hn : 5 ≤ n)
    (p : BallExtension.Parameters (Euclidean n)) {R : ℝ} (hR : 0 < R)
    {Ω : Set (Euclidean n)} (hΩ : IsCompact Ω)
    (hbad : Disjoint Ω (cubeBadSubspaceUnion n)) :
    ∃ (s : Finset {ξ : Euclidean n // ξ ∈ Ω ∧ (frozenSymbol n).h (0, ξ) = 0})
      (g : s → ComparisonGeometry (Euclidean n)) (r c C : ℝ) (A : Set (Euclidean n)),
      0 < r ∧ r < R ∧ 0 < c ∧ 0 < C ∧
      (∀ i : s, 3 * r < (g i).radius) ∧ IsCompact A ∧
      A ⊆ (cubeBadSubspaceUnion n)ᶜ ∧
      ∀ τ : ℝ, 0 < τ → ∃ δ ρ εx : ℝ, 0 < δ ∧ 0 < ρ ∧ ρ < τ ∧ 0 < εx ∧
      ∃ (centers : (i : s) → Finset (CanonicalPhase (g i).tangentSpace))
        (w : (i : s) → (q : centers i) → CanonicalFactorWeights q.1 ρ),
      ∀ (Q : Euclidean n → Fin n → MetricTensor n)
        (hQ : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞ Q x),
        cNorm (closedBall p.center p.radius) 6 (Q - fun _ ↦ cubeStress n) < δ →
        let H := normalizedHomogeneousSymbol isOpen_univ (affineFrameExtension p Q)
          (contDiff_affineFrameExtension p
            (fun x hx ↦ (hQ x hx).contDiffWithinAt)).contDiffOn;
        ∃ charts : (i : s) → ComparisonChart H (g i),
          (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
            c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
              ‖ComparisonChart.familyGradient charts η x‖ ≤ C ∧
              normalizedCovector (ComparisonChart.familyGradient charts η x) ∈ A) ∧
          (∀ x ∈ closedBall 0 r, ∀ ξ ∈ Ω, H.h (x, ξ) = 0 →
            ∃ η : ComparisonGeometry.ParameterFamily g,
              ξ = ComparisonChart.familyGradient charts η x) ∧
          (∀ i : s, (charts i).canonicalSource r ⊆ ⋃ q ∈ centers i, ball q (ρ / 8)) ∧
          (∀ i : s, ∀ q ∈ centers i, ∀ z ∈ closedBall q (2 * ρ),
            canonicalFlowLift z ∈ (charts i).chart.source ∧
              closedBall (canonicalState (charts i).flow z).1 εx ⊆ ball 0 (2 * r)) ∧
          (∀ i : s, ∀ z ∈ (charts i).canonicalSource r, ∃ q : centers i,
            (w i q).base 0 z.1 * (w i q).frequency z.2 = 1 ∧
            (w i q).base 1 z.1 * (w i q).frequency z.2 = 1) := by
  classical
  have hb (ξ) (hξ : ξ ∈ Ω) : ξ ∉ cubeBadSubspaceUnion n := disjoint_left.mp hbad hξ
  have hnz (ξ) (hξ : ξ ∈ Ω) : ξ ≠ 0 := by
    rintro rfl
    exact hb 0 hξ (zero_mem_cubeBadSubspaceUnion hn)
  have hsource : ({0} : Set (Euclidean n)) ×ˢ Ω ⊆ (frozenSymbol n).domain :=
    fun z hz ↦ (mem_frozenSymbol_domain z).mpr (hnz z.2 hz.2)
  obtain ⟨s, g, r₀, d₀, c, C, e, K, A, hr₀, _hd₀, hc, hC, _he,
    hK, hKD, _hsourceK, hri, hA, hAbad, _hAbuffer, hcover⟩ :=
    exists_finite_comparison_cover_with_uniform_rectangles (frozenSymbol n)
      (frozenSymbol n).isOpen_domain Subset.rfl (frozenSymbol_smooth n)
      (normalizedHomogeneousSymbol_conic isOpen_univ _ contDiffOn_const)
      (fun _ _ ↦ rfl) hΩ hsource hnz
      (fun ξ hξ hz ↦ frozenSymbol_hp_ne_zero hn (hb ξ hξ) hz)
      isOpen_univ (isClosed_cubeBadSubspaceUnion n)
      (fun ξ hξ ↦ ⟨mem_univ _, normalizedCovector_not_mem_cubeBadSubspaceUnion
        (hnz ξ hξ) (hb ξ hξ)⟩)
  let r := min r₀ R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrr₀ : r ≤ r₀ := by dsimp [r]; linarith [min_le_left r₀ R]
  have hrr : r < R := by dsimp [r]; linarith [min_le_right r₀ R]
  refine ⟨s, g, r, c, C, A, hr, hrr, hc, hC,
    fun i ↦ lt_of_le_of_lt (by linarith) (hri i), hA,
    fun q hq ↦ (hAbad hq).2, ?_⟩
  intro τ hτ
  obtain ⟨d, ρ, εx, centers, hd, _hdd, hρ, hρτ, hεx, hcharts⟩ :=
    hcover r hr hrr₀ τ hτ
  obtain ⟨δ, hδ, hsmall⟩ := exists_extended_symbol_comparison_radius p hK
    (fun z hz ↦ (mem_frozenSymbol_domain z).mp (hKD hz)) 3 hd
  choose w hw using fun i : s ↦ exists_canonicalFactorWeights_on_fixed_centers (centers i) hρ
  refine ⟨δ, ρ, εx, hδ, hρ, hρτ, hεx, centers, w, ?_⟩
  intro Q hQ hlow
  let hE := contDiff_affineFrameExtension p (fun x hx ↦ (hQ x hx).contDiffWithinAt)
  let H := normalizedHomogeneousSymbol isOpen_univ (affineFrameExtension p Q) hE.contDiffOn
  have hs : cNorm K 3 (fun z ↦ H.h z - (frozenSymbol n).h z) ≤ d :=
    (hsmall Q hQ ((cNorm_mono_order (by decide : 3 ≤ 6)).trans_lt hlow)).le
  obtain ⟨charts, hbounds, hv, hrect⟩ := hcharts H Subset.rfl
    (contDiffOn_normalizedSymbol isOpen_univ hE.contDiffOn)
    (normalizedHomogeneousSymbol_conic isOpen_univ _ hE.contDiffOn) hs
  exact ⟨charts,
    fun η x hx ↦ hbounds η x (closedBall_subset_closedBall (by linarith) hx),
    fun x hx ξ hξ hz ↦ hv x (closedBall_subset_closedBall hrr₀ hx) ξ hξ hz,
    fun i ↦ (hrect i).1, fun i ↦ (hrect i).2,
    fun i z hz ↦ hw i z ((hrect i).1 hz)⟩

end JanetCartan.ProtectedFlow
