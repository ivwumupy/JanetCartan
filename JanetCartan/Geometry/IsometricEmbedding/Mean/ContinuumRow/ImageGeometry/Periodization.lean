module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Periodization.Estimates
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# Quantitative periodization of locally smooth image coefficients

For `app:ch_background:defn:bg-row` and `app:ch_background:eq:bg-frame-tame`,
one fixed physical cutoff periodizes every entry of the reduced coefficient
array. The whole array need only be smooth on the larger physical ball.
The closed core has a plateau neighborhood, the order-zero bound has constant
one, and every full physical Fréchet derivative has a fixed linear bound.

The consumer is the geometric instantiation of `ContinuumRow.imageChannel`.
Its actual local-smoothness input is supplied by
`ImageGeometry.exists_reference_reduced_coefficient_estimates`. No image-channel
or geometric-neighborhood conclusion is asserted by this independent implication.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace JanetCartan.ContinuumRow.ImageGeometry.Periodization

open GeometricProfile

variable {n : ℕ}

private theorem cutCoefficient_support_box {χ : Euclidean n → ℝ} {r : ℝ}
    (hs : tsupport χ ⊆ Metric.ball 0 r)
    (q : Euclidean n → ReducedCoefficientIndex n → ℝ) (j : ReducedCoefficientIndex n) :
    tsupport (fun x ↦ χ x * q x j) ⊆ {x | ∀ i, |x i| ≤ r} := by
  intro x hx i
  have hx' := hs (tsupport_mul_subset_left hx)
  exact (PiLp.norm_apply_le x i).trans (mem_ball_zero_iff.mp hx').le

/-- Smoothness of each actual periodized coefficient of
`app:ch_background:defn:bg-row`, from local smoothness of the whole array. -/
theorem isSmoothPeriodic_cutCoefficient {χ : Euclidean n → ℝ} {r R : ℝ}
    (hrR : r < R) (hr : r < 1 / 2) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ Metric.ball 0 r)
    {q : Euclidean n → ReducedCoefficientIndex n → ℝ}
    (hq : ContDiffOn ℝ ∞ q (Metric.ball 0 R)) (j : ReducedCoefficientIndex n) :
    IsSmoothPeriodic (realPeriodization (fun x ↦ χ x * q x j)) := by
  apply isSmoothPeriodic_realPeriodization hr (cutCoefficient_support_box hs q j)
  exact (ContinuousLinearMap.proj j : (ReducedCoefficientIndex n → ℝ) →L[ℝ] ℝ).contDiff.comp
    (contDiff_cutReducedCoefficients hχ (hs.trans (Metric.ball_subset_ball hrR.le)) hq)

/-- The continuous real coefficient array for `app:ch_background:defn:bg-row`.
It uses one cutoff and the literal centered-representative formula for all entries. -/
def periodicReducedCoefficients {χ : Euclidean n → ℝ} {r R : ℝ}
    (hrR : r < R) (hr : r < 1 / 2) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ Metric.ball 0 r)
    (q : Euclidean n → ReducedCoefficientIndex n → ℝ)
    (hq : ContDiffOn ℝ ∞ q (Metric.ball 0 R)) :
    ReducedCoefficientIndex n → C(Torus n, ℝ) :=
  fun j ↦ ⟨realPeriodization (fun x ↦ χ x * q x j),
    (isSmoothPeriodic_cutCoefficient hrR hr hχ hs hq j).1⟩

/-- Expose the actual extension formula so the consumer can identify supported
operators using precisely the same arrays (`app:ch_background:defn:bg-row`). -/
@[simp] theorem periodicReducedCoefficients_apply {χ : Euclidean n → ℝ} {r R : ℝ}
    (hrR : r < R) (hr : r < 1 / 2) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ Metric.ball 0 r)
    (q : Euclidean n → ReducedCoefficientIndex n → ℝ)
    (hq : ContDiffOn ℝ ∞ q (Metric.ball 0 R)) (j : ReducedCoefficientIndex n) (z : Torus n) :
    periodicReducedCoefficients hrR hr hχ hs q hq j z =
      χ (AmplitudeBound.centeredTorusRepresentative z) *
        q (AmplitudeBound.centeredTorusRepresentative z) j := rfl

/-- On a neighborhood of every closed-core point, each lift is its original
uncut coefficient (`app:ch_background:defn:bg-row`). -/
theorem periodicReducedCoefficients_eventuallyEq {χ : Euclidean n → ℝ} {r₀ r R : ℝ}
    (h₀r : r₀ < r) (hrR : r < R) (hr : r < 1 / 2) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ Metric.ball 0 r)
    (hp : Metric.closedBall 0 r₀ ⊆ interior {x | χ x = 1})
    (q : Euclidean n → ReducedCoefficientIndex n → ℝ)
    (hq : ContDiffOn ℝ ∞ q (Metric.ball 0 R))
    (j : ReducedCoefficientIndex n) {x : Euclidean n} (hx : x ∈ Metric.closedBall 0 r₀) :
    periodicLift (periodicReducedCoefficients hrR hr hχ hs q hq j) =ᶠ[𝓝 x]
      (fun y ↦ q y j) := by
  have hcell : x ∈ fundamentalCell n := by
    intro i
    apply abs_le.mp
    exact (PiLp.norm_apply_le x i).trans
      ((mem_closedBall_zero_iff.mp hx).trans (by linarith))
  apply (realPeriodization_eventuallyEq hr (cutCoefficient_support_box hs q j) hcell).trans
  filter_upwards [isOpen_interior.mem_nhds (hp hx)] with y hy
  have hy' : y ∈ {x | χ x = 1} := interior_subset hy
  change χ y * q y j = q y j
  rw [show χ y = 1 from hy', one_mul]

/-- The full physical Fréchet derivatives of every periodic entry obey the
fixed cutoff bound (`app:ch_background:eq:bg-frame-tame`). -/
theorem norm_iteratedFDeriv_periodicReducedCoefficients_le
    {χ : Euclidean n → ℝ} {r R : ℝ}
    (hrR : r < R) (hr : r < 1 / 2) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ Metric.ball 0 r)
    (q : Euclidean n → ReducedCoefficientIndex n → ℝ)
    (hq : ContDiffOn ℝ ∞ q (Metric.ball 0 R))
    (m : ℕ) (j : ReducedCoefficientIndex n) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ m
      (periodicLift (periodicReducedCoefficients hrR hr hχ hs q hq j)) x‖ ≤
        cutoffDerivativeBound χ r m * cNorm (Metric.closedBall 0 r) m q := by
  apply norm_iteratedFDeriv_realPeriodization_le hr (cutCoefficient_support_box hs q j)
  intro y
  exact (norm_iteratedFDeriv_coefficient_le
    (contDiff_cutReducedCoefficients hχ (hs.trans (Metric.ball_subset_ball hrR.le)) hq)
    j m y).trans (norm_iteratedFDeriv_cutReducedCoefficients_le hrR hχ hs hq m y)

/-- The order-zero bound is sharp: multiplication by the fixed cutoff costs
no constant (`app:ch_background:defn:bg-row`). -/
theorem abs_periodicReducedCoefficients_le {χ : Euclidean n → ℝ} {r R : ℝ}
    (hrR : r < R) (hr : r < 1 / 2) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ Metric.ball 0 r) (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (q : Euclidean n → ReducedCoefficientIndex n → ℝ)
    (hq : ContDiffOn ℝ ∞ q (Metric.ball 0 R))
    (j : ReducedCoefficientIndex n) (z : Torus n) :
    |periodicReducedCoefficients hrR hr hχ hs q hq j z| ≤
      cNorm (Metric.closedBall 0 r) 0 q := by
  rw [periodicReducedCoefficients_apply]
  let x := AmplitudeBound.centeredTorusRepresentative z
  change |χ x * q x j| ≤ _
  by_cases hx : x ∈ tsupport χ
  · have hxr := Metric.ball_subset_closedBall (hs hx)
    have hqbound : ‖q x‖ ≤ cNorm (Metric.closedBall 0 r) 0 q := by
      simpa only [norm_iteratedFDeriv_zero] using
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall 0 r)
          (fun y hy ↦ ((hq y (Metric.closedBall_subset_ball hrR hy)).contDiffAt
            (Metric.isOpen_ball.mem_nhds (Metric.closedBall_subset_ball hrR hy))).of_le
              (show (0 : ℕ∞ω) ≤ ∞ by simp)) hxr (show 0 ≤ 0 from le_rfl)
    calc
      |χ x * q x j| = χ x * |q x j| := by rw [abs_mul, abs_of_nonneg (hχrange x).1]
      _ ≤ 1 * |q x j| := mul_le_mul_of_nonneg_right (hχrange x).2 (abs_nonneg _)
      _ ≤ ‖q x‖ := by simpa using norm_le_pi_norm (q x) j
      _ ≤ _ := hqbound
  · have hz : χ x = 0 := by
      by_contra h
      exact hx (subset_tsupport χ h)
    simpa only [hz, zero_mul, abs_zero] using cNorm_nonneg (Metric.closedBall 0 r) 0 q

/-- Choose one smooth physical cutoff and positive derivative constants before
the coefficient array and every differentiated order. This is the independent
periodization implication consumed by the geometric image-channel construction
(`app:ch_background:defn:bg-row`, `app:ch_background:eq:bg-frame-tame`).
All entries are retained, and the only regularity premise on the array is its
local smoothness on the larger ball. -/
theorem exists_cutoff_periodicReducedCoefficients (n : ℕ) {r₀ r₁ R : ℝ}
    (_hr₀ : 0 < r₀) (h₀₁ : r₀ < r₁) (h₁R : r₁ < R) (hR : R < 1 / 2) :
    ∃ (χ : Euclidean n → ℝ) (D : ℕ → ℝ),
      ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Metric.ball 0 r₁ ∧
      Metric.closedBall 0 r₀ ⊆ interior {x | χ x = 1} ∧ (∀ m, 0 < D m) ∧
      ∀ q : Euclidean n → ReducedCoefficientIndex n → ℝ,
        ContDiffOn ℝ ∞ q (Metric.ball 0 R) →
        ∃ c : ReducedCoefficientIndex n → C(Torus n, ℝ),
          (∀ j z, c j z = χ (AmplitudeBound.centeredTorusRepresentative z) *
            q (AmplitudeBound.centeredTorusRepresentative z) j) ∧
          (∀ j, IsSmoothPeriodic (c j)) ∧
          (∀ j x, x ∈ Metric.closedBall 0 r₀ →
            periodicLift (c j) =ᶠ[𝓝 x] (fun y ↦ q y j)) ∧
          (∀ m j x, ‖iteratedFDeriv ℝ m (periodicLift (c j)) x‖ ≤
            D m * cNorm (Metric.closedBall 0 r₁) m q) ∧
          (∀ j z, |c j z| ≤ cNorm (Metric.closedBall 0 r₁) 0 q) := by
  obtain ⟨χ, hχ, hχrange, hcompact, hs, hp⟩ :=
    CompatibleResponse.exists_compact_family_cutoff
      (isCompact_closedBall (0 : Euclidean n) r₀) Metric.isOpen_ball
      (Metric.closedBall_subset_ball h₀₁)
  refine ⟨χ, cutoffDerivativeBound χ r₁, hχ, hχrange, hcompact, hs, hp,
    cutoffDerivativeBound_pos χ r₁, ?_⟩
  intro q hq
  refine ⟨periodicReducedCoefficients h₁R (h₁R.trans hR) hχ hs q hq, ?_, ?_, ?_, ?_, ?_⟩
  · exact periodicReducedCoefficients_apply h₁R (h₁R.trans hR) hχ hs q hq
  · exact isSmoothPeriodic_cutCoefficient h₁R (h₁R.trans hR) hχ hs hq
  · intro j x hx
    exact periodicReducedCoefficients_eventuallyEq h₀₁ h₁R (h₁R.trans hR) hχ hs hp q hq j hx
  · exact norm_iteratedFDeriv_periodicReducedCoefficients_le h₁R (h₁R.trans hR) hχ hs q hq
  · exact abs_periodicReducedCoefficients_le h₁R (h₁R.trans hR) hχ hs hχrange q hq

end JanetCartan.ContinuumRow.ImageGeometry.Periodization
