module

public import JanetCartan.Geometry.IsometricEmbedding.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.LocalTarget
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.Smallness

/-!
# Target initialization after fixing a reference

The target half of `main:prop:seed`, including local coordinate normalization,
`main:eq:seed-small` for a locally smooth metric, and one positive dilation for
finitely many requested accuracies. The reference and its positive source scale
are inputs fixed before those accuracies.

The complete construction is `exists_fixed_reference_initialization` in
`Reference.Initialization.Assembly`: it constructs the analytic source, its
fixed dilation, actual carrier gaps and normal neighborhood, then supplies one
common target interval for initialization and history smoothing. This entry
module retains the target estimates used by `IterationInput` and
`ScaledReference`; the assembly imports those consumers, avoiding an import
cycle here.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan

/-- `main:prop:seed`, `main:eq:seed-small`: for a fixed flat reference and source
scale, a normalized local metric admits one interval of domain-valid dilations
and uniform estimates at every order. No global smoothness is assumed. -/
theorem local_target_bounds_for_fixed_reference {n : ℕ} (G : FlatReference n)
    {ρ : ℝ} (hρ : 0 < ρ) {g : MetricField n} {U : Set (Euclidean n)}
    (hU : IsOpen U) (h0 : (0 : Euclidean n) ∈ U)
    (hg : IsRiemannianMetricOn g U) (hg0 : g 0 = 1) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
      (∀ s ∈ Icc (0 : ℝ) s₀,
        (∀ x ∈ G.domain.closureChart n, (s * ρ) • x ∈ U) ∧
        IsRiemannianMetricOn (scaledMetric g (s * ρ)) (G.domain.closureChart n)) ∧
      ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Icc (0 : ℝ) s₀,
        cNorm (G.domain.closureChart n) r
          (scaledMetric g (s * ρ) - inducedMetric G.map) ≤ C * s := by
  obtain ⟨s₀, hs₀, hs₁, hdom, hb⟩ :=
    exists_local_target_dilation_bounds G.domain hρ hU h0 hg.1 hg0
  refine ⟨s₀, hs₀, hs₁, ?_, ?_⟩
  · intro s hs
    exact ⟨hdom s hs,
      (contDiffOn_scaledMetric hg.1 (s * ρ)).mono (hdom s hs),
      fun x hx ↦ hg.2 _ (hdom s hs x hx)⟩
  · have hflat : inducedMetric G.map = fun _ ↦ 1 := funext G.inducedMetric_eq_one
    simpa only [scaledMetric, hflat, Pi.sub_def] using hb

/-- `main:prop:seed`: normalize the local metric and, after the reference and its
scale are fixed, meet any finite list of derivative thresholds with one positive
target dilation. The coordinate change and admissible parameter interval are
chosen before all thresholds and extra upper bounds on that dilation.

This is the target-selection part of initialization, conditional only on the
explicit fixed `FlatReference`; it does not assert existence of that reference
or its required carrier and analytic neighborhoods. -/
theorem exists_normalized_small_target_for_reference {n : ℕ} (G : FlatReference n)
    {ρ : ℝ} (hρ : 0 < ρ) {g : MetricField n} {U : Set (Euclidean n)}
    (hU : IsOpen U) (h0 : (0 : Euclidean n) ∈ U) (hg : IsRiemannianMetricOn g U) :
    ∃ A : MetricTensor n, IsUnit A ∧ coordinatePullback g A 0 = 1 ∧
      ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
        ∀ (orders : Finset ℕ) (ε : ℕ → ℝ), (∀ r ∈ orders, 0 < ε r) →
          ∀ δ : ℝ, 0 < δ → ∃ s : ℝ, 0 < s ∧ s ≤ s₀ ∧ s ≤ δ ∧
            (∀ x ∈ G.domain.closureChart n, coordinateMap A ((s * ρ) • x) ∈ U) ∧
            IsRiemannianMetricOn (scaledMetric (coordinatePullback g A) (s * ρ))
              (G.domain.closureChart n) ∧
            ∀ r ∈ orders, cNorm (G.domain.closureChart n) r
              (scaledMetric (coordinatePullback g A) (s * ρ) - inducedMetric G.map) < ε r := by
  obtain ⟨A, hA, hV, hV0, hgA, hgA0⟩ := exists_normalized_coordinates hU h0 hg
  obtain ⟨s₀, hs₀, hs₁, hdom, hb⟩ :=
    local_target_bounds_for_fixed_reference G hρ hV hV0 hgA hgA0
  choose C hC hbound using hb
  refine ⟨A, hA, hgA0, s₀, hs₀, hs₁, ?_⟩
  intro orders ε hε δ hδ
  obtain ⟨s, hs, hsMax, hsε⟩ :=
    exists_scale_for_finite_thresholds orders C ε hC hε (lt_min hs₀ hδ)
  have hss₀ := hsMax.trans (min_le_left s₀ δ)
  have hsδ := hsMax.trans (min_le_right s₀ δ)
  have hsI : s ∈ Icc (0 : ℝ) s₀ := ⟨hs.le, hss₀⟩
  exact ⟨s, hs, hss₀, hsδ, (hdom s hsI).1, (hdom s hsI).2,
    fun r hr ↦ (hbound r s hsI).trans_lt (hsε r hr)⟩

end JanetCartan
