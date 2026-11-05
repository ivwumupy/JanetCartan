module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.InitialScalar
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition

/-!
# The original positive-density class supplies the leading scalar inputs

The consumer `exists_local_leading_carrier_primitives` needs a positive lower
bound and a C15 upper bound on its SAME initial scalar. These are derived for
the literal `σ * sqrt (1 + v)`, with constants before the density. The tame
estimate also gives a single high density norm, without changing the carrier
measure or transport footpoint. Sources: `app:ch_background:prop:bg-frame`,
`app:ch_background:prop:bg-positive`, `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumRow.LeadingPrimitive.DensityScalar
open CanonicalCarrier ProjectedStressFrame

/-- Uniform positive lower and C15 upper bounds for the prescribed density
class. The constant precedes even the initial ball and source scale. These
are exactly the scalar inputs of `exists_local_leading_carrier_primitives`
(`app:ch_background:prop:bg-frame`, `app:ch_waves:thm:leading`). -/
theorem exists_initial_leading_bounds (n : ℕ) :
    ∃ C > (0 : ℝ),
      ∀ (p : Euclidean (n - 1) × Euclidean 3) {R : ℝ}, 0 < R →
      ∀ {σ : ℝ}, 0 < σ →
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
        ContDiffOn ℝ ∞ v (ball p (R / 4)) →
        (∀ q ∈ ball p (R / 4), 0 < 1 + v q) →
        (∀ q ∈ closedBall p (R / 8), 1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
        cNorm (closedBall p (R / 8)) 15 v ≤ 1 →
        let initial := fun q ↦ positiveDensityAmplitude σ (v q)
        0 < σ * Real.sqrt (1 / 2) ∧
        0 ≤ σ * C ∧
        ContDiffOn ℝ ∞ initial (ball p (R / 4)) ∧
        cNorm (closedBall p (R / 8)) 15 initial ≤ σ * C ∧
        (∀ q ∈ ball p (R / 8), σ * Real.sqrt (1 / 2) ≤ initial q) ∧
        (∀ q ∈ ball p (R / 8), initial q ^ 2 = σ ^ 2 * (1 + v q)) := by
  obtain ⟨C, hC, hb⟩ := exists_density_initial_scalar_bound n 15
  refine ⟨C, hC, ?_⟩
  intro p R hR σ hσ v hv hpos hinterval hnorm
  obtain ⟨hreg, _, hsq, hbound⟩ := hb p hR hσ v hv hpos hinterval hnorm
  exact ⟨mul_pos hσ (Real.sqrt_pos.mpr (by norm_num)), (mul_pos hσ hC).le,
    hreg, hbound, fun q hq ↦
      (positiveDensityAmplitude_mem_Icc hσ.le (hinterval q (ball_subset_closedBall hq))).1,
    hsq⟩

/-- One-high scalar estimate on the actual buffered initial ball. The scale
and density vary after the constants. Together with `exists_initial_leading_bounds`
this covers the original positive-density class while the continuum-row
primitive theorem keeps its stated additive initial-scalar budget
(`app:ch_background:eq:bg-mixed-input`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_initial_scalar_tame_bounds (n : ℕ)
    (p : Euclidean (n - 1) × Euclidean 3) {R : ℝ} (hR : 0 < R) :
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      ∀ (σ : ℝ), 0 ≤ σ →
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
        ContDiffOn ℝ ∞ v (ball p (R / 4)) →
        (∀ q ∈ ball p (R / 4), 0 < 1 + v q) →
        (∀ q ∈ closedBall p (R / 8), 1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
        ∀ j, cNorm (closedBall p (R / 8)) j
            (fun q ↦ positiveDensityAmplitude σ (v q)) ≤
          σ * A j * (1 + cNorm (closedBall p (R / 8)) j v) := by
  let g : ℝ → ℝ := fun t ↦ Real.sqrt (1 + t)
  have hg (j : ℕ) (t : ℝ) (ht : t ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
      ContDiffAt ℝ j g t :=
    (contDiffAt_const.add contDiffAt_id).sqrt (by dsimp; linarith [ht.1])
  choose A hA hb using fun j : ℕ ↦ exists_cNorm_comp_le_tame_closedBall_contDiffOn
    p (by positivity : 0 < R / 8) isCompact_Icc (le_refl j) (hg j)
  refine ⟨A, hA, ?_⟩
  intro σ hσ v hv _hpos hinterval j
  have hmap : MapsTo v (closedBall p (R / 8)) (Icc (-1 / 2 : ℝ) (1 / 2)) := by
    intro q hq
    have hh := hinterval q hq
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hKO : closedBall p (R / 8) ⊆ ball p (R / 4) := closedBall_subset_ball (by linarith)
  have hgcomp : ∀ q ∈ closedBall p (R / 8), ContDiffAt ℝ j (g ∘ v) q := by
    intro q hq
    exact (hg j _ (hmap hq)).comp q
      ((hv.contDiffAt (isOpen_ball.mem_nhds (hKO hq))).of_le (by simp))
  change cNorm _ j (σ • (g ∘ v)) ≤ _
  rw [cNorm_smul_of_contDiffAt σ hgcomp, Real.norm_eq_abs, abs_of_nonneg hσ]
  exact (mul_le_mul_of_nonneg_left
    (hb j (ball p (R / 4)) isOpen_ball hKO v hv hmap) hσ).trans_eq (mul_assoc _ _ _).symm

end JanetCartan.ContinuumRow.LeadingPrimitive.DensityScalar
