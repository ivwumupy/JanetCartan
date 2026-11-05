module

public import JanetCartan.Analysis.ContDiff.PositiveSquareRoot
public import JanetCartan.Analysis.ContDiff.Norm.Composition
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Basic

/-!
# The prescribed positive initial scalar on the actual flow domain

For the density class in `app:ch_background:prop:bg-frame`, the literal scalar
is `σ * sqrt (1 + v)`. Its finite-order bound below is uniform in the initial
ball as well as the density. Thus the scalar budget may be chosen before the
flow radius returned by `ActualPrimitive`, without assuming a bound on the
resulting scalar or requiring positivity outside the actual initial domain.

This is the scalar input of `exists_actual_canonical_carrier`; it does not
construct the later inverse-dependent positive background or prepared density.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumRow.CanonicalCarrier

/-- The density class of `app:ch_background:prop:bg-frame` supplies the actual
finite initial-scalar budget. Constants precede the domain, source scale and
density. Smoothness and positivity are required only on the buffered initial
ball; the quantitative density interval is used on its compact subball.
The consumer uses orders `15` and `2 * (n + 1) + 14` in the local carrier
construction (`app:ch_background:eq:bg-mixed-input`, `bg-T`). -/
theorem exists_density_initial_scalar_bound (n m : ℕ) :
    ∃ C > (0 : ℝ),
      ∀ (p : Euclidean (n - 1) × Euclidean 3) {R : ℝ}, 0 < R →
      ∀ {σ : ℝ}, 0 < σ →
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
        ContDiffOn ℝ ∞ v (ball p (R / 4)) →
        (∀ q ∈ ball p (R / 4), 0 < 1 + v q) →
        (∀ q ∈ closedBall p (R / 8), 1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
        cNorm (closedBall p (R / 8)) m v ≤ 1 →
        ContDiffOn ℝ ∞ (fun q ↦ positiveDensityAmplitude σ (v q)) (ball p (R / 4)) ∧
        (∀ q ∈ ball p (R / 8), 0 < positiveDensityAmplitude σ (v q)) ∧
        (∀ q ∈ ball p (R / 8),
          positiveDensityAmplitude σ (v q) ^ 2 = σ ^ 2 * (1 + v q)) ∧
        cNorm (closedBall p (R / 8)) m
          (fun q ↦ positiveDensityAmplitude σ (v q)) ≤ σ * C := by
  let I : Set ℝ := Icc (-1 / 2) (1 / 2)
  let g : ℝ → ℝ := fun t ↦ Real.sqrt (1 + t)
  have hg (t : ℝ) (ht : t ∈ I) : ContDiffAt ℝ m g t :=
    (contDiffAt_const.add contDiffAt_id).sqrt (by dsimp [I] at ht; dsimp; linarith [ht.1])
  let B := compositionMultiplicity m * cNorm I m g * (2 : ℝ) ^ m
  have hmult : 0 ≤ compositionMultiplicity m :=
    Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hmult (cNorm_nonneg ..)) (by positivity)
  refine ⟨B + 1, by positivity, ?_⟩
  intro p R hR σ hσ v hv hpos hinterval hnorm
  let K := closedBall p (R / 8)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKO : K ⊆ ball p (R / 4) := closedBall_subset_ball (by linarith)
  have hvAt (q) (hq : q ∈ K) : ContDiffAt ℝ m v q :=
    (hv.contDiffAt (isOpen_ball.mem_nhds (hKO hq))).of_le (by simp)
  have hvI : MapsTo v K I := by
    intro q hq
    obtain ⟨h₁, h₂⟩ := hinterval q hq
    exact ⟨by linarith, by linarith⟩
  have hgcomp (q) (hq : q ∈ K) : ContDiffAt ℝ m (g ∘ v) q :=
    (hg (v q) (hvI hq)).comp q (hvAt q hq)
  have hcomp : cNorm K m (g ∘ v) ≤ B := by
    apply (cNorm_comp_le_polynomial hvAt (fun q hq ↦ hg (v q) (hvI hq))
      (fun _ hj ↦ bddAbove_norm_iteratedFDeriv_of_contDiffAt hK hvAt hj)
      (cNorm_nonneg I m g) ?_).trans
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith [cNorm_nonneg K m v])
          (by linarith : 1 + cNorm K m v ≤ 2) m)
        (mul_nonneg hmult (cNorm_nonneg ..))
    · intro j hj q hq
      exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt isCompact_Icc hg (hvI hq) hj
  refine ⟨contDiffOn_positiveDensityAmplitude σ hv hpos,
    fun q hq ↦ positiveDensityAmplitude_pos hσ
      (hpos q (ball_subset_ball (by linarith) hq)),
    fun q hq ↦ positiveDensityAmplitude_sq
      (hpos q (ball_subset_ball (by linarith) hq)).le, ?_⟩
  change cNorm K m (σ • (g ∘ v)) ≤ σ * (B + 1)
  rw [cNorm_smul_of_contDiffAt σ hgcomp, Real.norm_eq_abs, abs_of_pos hσ]
  exact mul_le_mul_of_nonneg_left (hcomp.trans (by linarith)) hσ.le

end JanetCartan.ContinuumRow.CanonicalCarrier
