module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Buffers
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.SobolevNorm
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Fixed localization and the actual raw slice window

The cutoff in `app:ch_waves:eq:individual-raw-slice` only enters the norm.
Its plateau, compact support and adapted-coordinate support are proved here.
The same rounded Fourier ceiling and every dyadic epsilon fit the original
domains of `exists_canonicalSliceNormalData` under one frequency window.
No physical wave or initial Fourier mask is changed.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.RawPrimary
open SliceGeometry SliceBounds RawInputPartition
open ActualCarriers FrozenMenu CurrentFullPhase

/-- Construct the fixed norm cutoff with a nonempty plateau and the exact
spatial and time supports required by the sharp slice endpoint
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_rawSlice_measurementCutoff {n : ℕ} {ξ : Euclidean n}
    (sec : ActualCarriers.FrozenPhaseReference.AdaptedSection ξ)
    {a : ℝ} (ha : 0 < a) :
    ∃ χ : Euclidean n → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      EqOn χ 1 (closedBall 0 (a / 8)) ∧
      tsupport χ ⊆ closedBall 0 (a / 4) ∧
      tsupport χ ⊆ slicePhysicalDomain n a ∧
      (∀ q, χ (adaptedPhysicalCoordinates sec q) ≠ 0 → q.2 ∈ sliceSpatialCore n a) ∧
      (∀ x ∈ tsupport χ, ((adaptedPhysicalCoordinates sec).symm x).1 ∈ Ioo (-a) a) := by
  let χ : ContDiffBump (0 : Euclidean n) := ⟨a / 8, a / 4, by positivity, by linarith⟩
  have hs : tsupport χ = closedBall 0 (a / 4) := χ.tsupport_eq
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, ?_, ?_, hs.subset, ?_, ?_, ?_⟩
  · intro x
    exact ⟨χ.nonneg, χ.le_one⟩
  · intro x hx
    exact χ.one_of_mem_closedBall hx
  · rw [hs]
    exact closedBall_subset_ball (by linarith)
  · intro q hq
    have hx : adaptedPhysicalCoordinates sec q ∈ tsupport χ := subset_tsupport _ hq
    rw [hs] at hx
    have hx' : ‖adaptedPhysicalCoordinates sec q‖ ≤ a / 4 := by simpa using hx
    have hc := norm_adaptedPhysicalCoordinates_symm_le sec (adaptedPhysicalCoordinates sec q)
    rw [MeasurableEquiv.symm_apply_apply] at hc
    have hy := (norm_snd_le q).trans (hc.trans hx')
    change dist q.2 0 ≤ a / 2
    rw [dist_zero_right]
    linarith
  · intro x hx
    rw [hs] at hx
    have hx' : ‖x‖ ≤ a / 4 := by simpa using hx
    have ht := (norm_fst_le ((adaptedPhysicalCoordinates sec).symm x)).trans
      ((norm_adaptedPhysicalCoordinates_symm_le sec x).trans hx')
    rw [Real.norm_eq_abs] at ht
    exact abs_lt.mp (ht.trans_lt (by linarith))

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The manuscript's unchanged rounded band labels fit the epsilon range
of the SAME slice normal geometry (`app:ch_waves:eq:individual-raw-slice`). -/
theorem rawSlice_dyadic_epsilon_mem {K τ e : ℝ} (hK : 1 ≤ K) (hτ : 0 ≤ τ)
    (hwindow : 2 * (τ * K) ≤ e) (j : Fin (cutoffCount K)) :
    τ * (2 : ℝ) ^ j.val ∈ Icc 0 e := by
  have hj := (lt_cutoffCount_iff hK j.val).mp j.isLt
  have hp : (2 : ℝ) ^ j.val ≤ 2 * K := by
    dsimp only [dyadicScale] at hj
    linarith
  exact ⟨mul_nonneg hτ (by positivity),
    (mul_le_mul_of_nonneg_left hp hτ).trans (by nlinarith [hwindow])⟩

/-- All shift premises of the sharp slice theorem follow from the retained
domain radii and one window. This includes the radius-four input extension,
every original smooth band, and the full rounded `4 K` Fourier ceiling
(`app:ch_waves:thm:individual`). -/
theorem rawSlice_window_containments (z : Euclidean 3) {a b e K τ : ℝ}
    (he : 0 < e) (heb : 16 * e < b) (hK : 1 ≤ K) (hτ : 0 ≤ τ)
    (hwindow : 2 * (τ * K) ≤ e) :
    (∀ j : Fin (cutoffCount K), τ * (2 : ℝ) ^ j.val ∈ Icc 0 e) ∧
    (∀ j : Fin (cutoffCount K), ∀ x ∈ sliceAdaptedDomain T a,
      ∀ θ ∈ sliceInputExtension n,
        (τ * (2 : ℝ) ^ j.val, x, θ) ∈ sliceShiftDomain T a e) ∧
    (∀ j : Fin (cutoffCount K), ∀ θ ∈ sliceInputExtension n,
      T.reference.spatialPatch z + (τ * (2 : ℝ) ^ j.val) • θ ∈
        ball (T.reference.spatialPatch z) b) ∧
    (∀ η ∈ closedBall 0 (4 * K), T.reference.spatialPatch z + τ • η ∈
      ball (T.reference.spatialPatch z) b) := by
  have hε := rawSlice_dyadic_epsilon_mem hK hτ hwindow
  refine ⟨hε, ?_, ?_, ?_⟩
  · intro j x hx θ hθ
    exact ⟨sliceParameterDomain_contains he (hε j), hx, hθ⟩
  · intro j θ hθ
    have hn : ‖θ‖ ≤ 4 := (mem_ball_zero_iff.mp hθ).le
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hε j).1]
    have hbound := mul_le_mul (hε j).2 hn (norm_nonneg _) he.le
    linarith
  · intro η hη
    have hn : ‖η‖ ≤ 4 * K := by simpa using hη
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hτ]
    have hbound := mul_le_mul_of_nonneg_left hn hτ
    nlinarith

/-- The slice geometry can be capped by the SAME corrected working ball.
The resulting original amplitude domain lies in that ball before any Fourier
integration (`app:ch_waves:eq:individual-grading`). -/
theorem rawSlice_product_subset_workingBall {σ a b : ℝ} (hσ : 0 < σ)
    (ha : 4 * a ≤ σ / 2) (hb : b ≤ σ / 4)
    (z₀ z : Euclidean 3) (ζ₀ : Euclidean (n - 1))
    (hz : (z, T.reference.spatialPatch z) ∈ ball (z₀, ζ₀) (σ / 4)) :
    ∀ q ∈ slicePhysicalDomain n a ×ˢ ball (T.reference.spatialPatch z) b,
      (q.1, (z, q.2)) ∈ closedBall ((0 : Euclidean n), (z₀, ζ₀)) σ := by
  intro q hq
  exact rawFamily_product_subset_workingBall hσ z₀ z ζ₀ (T.reference.spatialPatch z) hz
    (ball_subset_ball ha hq.1) (ball_subset_ball hb hq.2)

end JanetCartan.RawPrimary
