module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.MaskProfiles.Bounds

/-!
# Proven fixed-mask inputs for the canonical raw slice estimate

This module supplies the missing normalized-mask premises of
`CanonicalSlice.exists_canonical_rawSliceSobolev` and
`SliceBounds.exists_rawPhysicalSliceSobolev_wkbGrades`, for the literal
`sqrt ‖θ‖ * weightedRadialBand mask j (2^j • θ)`.
The original half-size dyadic scales, wide bands, complex detector, and
entire floor-one high-pass transition are unchanged.

Only primitive smoothness, positive degree-zero homogeneity and the original
high-pass properties are inputs. The parent must instantiate these for its
selected detector and cutoff; no successful raw family is assumed here.
See `app:ch_waves:eq:B-bounds` and `app:ch_waves:eq:individual-raw-slice`.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.RawPrimary.MaskProfiles
open SliceBounds SliceGeometry

/-- All fixed-mask premises of the canonical raw slice consumer, derived
for the SAME angular detector, high-pass, physical cutoff and retained
adapted section. In particular the original high-pass transition is kept
and no normalized-mask seminorm is assumed
(`app:ch_waves:eq:B-bounds`, `app:ch_waves:eq:individual-raw-slice`). -/
theorem canonicalSlice_mask_premises {n : ℕ}
    {ξ : Euclidean n} (sec : ActualCarriers.FrozenPhaseReference.AdaptedSection ξ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (a : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ a θ)
    (hah : ∀ r : ℝ, 0 < r → ∀ θ, a (r • θ) = a θ)
    (hH : ContDiff ℝ ∞ H) (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0)
    (hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1) (ρ e : ℝ) :
    Measurable (detectorMask a H) ∧
    (∃ Md : ℝ, ∀ η, ‖detectorMask a H η‖ ≤ Md) ∧
    (∀ j, ContDiffOn ℝ ∞ (normalizedMask a H j) (sliceInputExtension n)) ∧
    (∀ j, Function.support (normalizedMask a H j) ⊆ sliceInputCore n) ∧
    (∀ j, tsupport (normalizedMask a H j) ⊆ sliceInputExtension n) ∧
    ∃ bmask : ℕ → ℝ, (∀ k, 0 ≤ bmask k) ∧
      ∀ j, ∀ q ∈ sliceClosedCore n ρ e, ∀ k,
        ‖iteratedFDeriv ℝ k
          (fun w : ℝ × (ℝ × Euclidean (n - 1)) × Euclidean (n - 1) ↦
            (χ (adaptedPhysicalCoordinates sec w.2.1) : ℂ) * normalizedMask a H j w.2.2) q‖ ≤
              bmask k := by
  obtain ⟨Md, _, hMd⟩ := exists_bound_detectorMask a H ha hah hH hH₀ hH₁
  refine ⟨(contDiff_detectorMask a H ha hH hH₀).continuous.measurable,
    ⟨Md, hMd⟩, fun j ↦ (contDiff_normalizedMask a H ha hH j).contDiffOn,
    support_normalizedMask_subset a H, ?_,
    exists_sliceClosedCore_mask_bounds sec χ hχ a H ha hah hH hH₁ ρ e⟩
  intro j
  exact (tsupport_normalizedMask_subset a H j).trans
    (Metric.closedBall_subset_ball (by norm_num))

end JanetCartan.RawPrimary.MaskProfiles
