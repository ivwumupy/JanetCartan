module

public import JanetCartan.Analysis.Sobolev.Local.Embedding.SmoothOneDimension.RealLine
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Calculus.Deriv.Linear

/-!
# The smooth local Sobolev estimate in dimension one

This proves the one-dimensional smooth H¹-to-L⁴ bound used in
`app:ch_regular:thm:exact-correction`, with the derivative norm convention of
`app:not:fourier`. The real-line estimate is transported along the
measure-preserving linear isometry furnished by the singleton orthonormal basis.
No compact-support condition is required.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff

@[expose] public noncomputable section

namespace JanetCartan.LocalSobolev

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The pointwise H¹ bound on one-dimensional Euclidean space
(`app:ch_regular:thm:exact-correction`). Both global L² norms are transported
explicitly from Euclidean volume to Lebesgue measure on the real line. -/
theorem enorm_le_eLpNorm_two_add_iteratedFDeriv_one_dimension
    {g : EuclideanSpace ℝ (Fin 1) → F} (hg : ContDiff ℝ 1 g)
    (x : EuclideanSpace ℝ (Fin 1)) :
    ‖g x‖ₑ ≤ eLpNorm g 2 volume + eLpNorm (iteratedFDeriv ℝ 1 g) 2 volume := by
  let e := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  have he : MeasurePreserving e volume volume := e.measurePreserving
  have hf : ContDiff ℝ 1 (g ∘ e) := hg.comp e.contDiff
  have hderiv (t : ℝ) : ‖deriv (g ∘ e) t‖ ≤ ‖iteratedFDeriv ℝ 1 g (e t)‖ := by
    have hchain : HasDerivAt (g ∘ e) (fderiv ℝ g (e t) (e 1)) t :=
      (hg.differentiable one_ne_zero (e t)).hasFDerivAt.comp_hasDerivAt t
        e.toContinuousLinearMap.hasDerivAt
    rw [hchain.deriv, norm_iteratedFDeriv_one]
    have he1 : ‖e (1 : ℝ)‖ = 1 := (e.norm_map 1).trans (norm_one (α := ℝ))
    have hop := (fderiv ℝ g (e t)).le_opNorm (e 1)
    rwa [he1, mul_one] at hop
  have hd : eLpNorm (deriv (g ∘ e)) 2 volume ≤
      eLpNorm (iteratedFDeriv ℝ 1 g) 2 volume := by
    apply (eLpNorm_mono (hf.continuous_deriv le_rfl).aestronglyMeasurable hderiv).trans
    exact le_of_eq (eLpNorm_comp_measurePreserving
      (hg.continuous_iteratedFDeriv (by norm_num)).aestronglyMeasurable he)
  have h := enorm_le_eLpNorm_two_add_deriv hf (e.symm x)
  simp only [Function.comp_apply, e.apply_symm_apply] at h
  rw [eLpNorm_comp_measurePreserving hg.continuous.aestronglyMeasurable he] at h
  exact h.trans (add_le_add_right hd _)

/-- Integrating the pointwise H¹ bound on a ball gives the smooth local L⁴
estimate in dimension one (`app:ch_regular:thm:exact-correction`). -/
theorem eLpNorm_four_le_one_dimension {g : EuclideanSpace ℝ (Fin 1) → F}
    (hg : ContDiff ℝ 1 g) (c : EuclideanSpace ℝ (Fin 1)) (R : ℝ) :
    eLpNorm g 4 (volume.restrict (Metric.ball c R)) ≤
      volume (Metric.ball c R) ^ (1 / 4 : ℝ) *
        (eLpNorm g 2 volume + eLpNorm (iteratedFDeriv ℝ 1 g) 2 volume) := by
  have h := eLpNorm_le_of_ae_enorm_bound (p := 4)
    (μ := volume.restrict (Metric.ball c R)) hg.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (enorm_le_eLpNorm_two_add_iteratedFDeriv_one_dimension hg))
  simpa [Measure.restrict_apply_univ, smul_eq_mul, mul_comm, one_div] using h

/-- The one-dimensional smooth estimate needed to pass to weak local H¹ spaces
in `app:ch_regular:thm:exact-correction`. One may choose the exponent to be four;
the positive constant depends only on the ball. -/
theorem exists_smooth_eLpNorm_le_one_dimension [FiniteDimensional ℝ F]
    (c : EuclideanSpace ℝ (Fin 1)) {R : ℝ} (_hR : 0 < R) :
    ∃ p C : ℝ≥0, 2 < p ∧ 0 < C ∧
      ∀ g : EuclideanSpace ℝ (Fin 1) → F,
        ContDiff ℝ ∞ g → MemLp g 2 volume →
        MemLp (iteratedFDeriv ℝ 1 g) 2 volume →
        eLpNorm g p (volume.restrict (Metric.ball c R)) ≤ (C : ℝ≥0∞) *
          (eLpNorm g 2 volume + eLpNorm (iteratedFDeriv ℝ 1 g) 2 volume) := by
  let A : ℝ≥0∞ := volume (Metric.ball c R) ^ (1 / 4 : ℝ)
  have hA : A ≠ ⊤ := by
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_ne_top
  refine ⟨4, A.toNNReal + 1, by norm_num, by positivity, ?_⟩
  intro g hg _hg₀ _hg₁
  apply (eLpNorm_four_le_one_dimension (hg.of_le (by norm_num)) c R).trans
  apply mul_le_mul_left
  change A ≤ ((A.toNNReal + 1 : ℝ≥0) : ℝ≥0∞)
  rw [ENNReal.coe_add, ENNReal.coe_toNNReal hA]
  exact le_self_add

end JanetCartan.LocalSobolev
