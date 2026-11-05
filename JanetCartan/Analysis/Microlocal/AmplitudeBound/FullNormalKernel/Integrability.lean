module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Integrability of compact normal kernels

The compact joint support of the smooth kernel in
`app:ch_osc:eq:two-position-normal-bound` in `paper.tex` makes its normal
kernel weight integrable for L² inputs and L∞ multipliers. No finiteness
assumption on the parameter domain is needed.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff

namespace JanetCartan.AmplitudeBound

variable {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin m))}

/-- The weight in the full normal kernel is absolutely integrable on the product
space for every L² input and L∞ multiplier
(`app:ch_osc:eq:two-position-normal-bound`). Compact projections of the joint
support suffice, even when the parameter domain has infinite measure. -/
theorem integrable_fullNormalAmplitudeKernel_weight
    (t : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) → ℂ)
    (ht : ContDiff ℝ ∞ (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t))
    (g : Lp ℂ ∞ (volume.restrict D))
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin m) ↦
      t x p.2 * star (t p.1 p.2) * g p.2 * f p.1)
      (volume.prod (volume.restrict D)) := by
  let K := tsupport (Function.uncurry t)
  let X := Prod.fst '' K
  let U := Prod.snd '' K
  have hX : IsCompact X := hs.image continuous_fst
  have hU : IsCompact U := hs.image continuous_snd
  have hfi : Integrable (X.indicator (f : EuclideanSpace ℝ (Fin d) → ℂ)) :=
    ((Lp.memLp f).locallyIntegrable (by norm_num)).integrableOn_isCompact hX
      |>.integrable_indicator hX.measurableSet
  have hgi : Integrable (U.indicator (g : EuclideanSpace ℝ (Fin m) → ℂ))
      (volume.restrict D) :=
    ((Lp.memLp g).locallyIntegrable (by simp)).integrableOn_isCompact hU
      |>.integrable_indicator hU.measurableSet
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous ht.continuous
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (0, 0))
  have hm : Continuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin m) ↦
      t x p.2 * star (t p.1 p.2)) :=
    (ht.continuous.comp (continuous_const.prodMk continuous_snd)).mul ht.continuous.star
  have hb : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin m),
      ‖t x p.2 * star (t p.1 p.2)‖ ≤ C * C := by
    intro p
    rw [norm_mul, norm_star]
    exact mul_le_mul (hC (x, p.2)) (hC p) (norm_nonneg _) hC0
  apply ((hfi.mul_prod hgi).bdd_mul hm.aestronglyMeasurable
    (Eventually.of_forall hb)).congr
  apply Eventually.of_forall
  intro p
  by_cases hp : t p.1 p.2 = 0
  · simp [hp]
  · have hpK : p ∈ K := subset_tsupport (Function.uncurry t) hp
    have hpX : p.1 ∈ X := ⟨p, hpK, rfl⟩
    have hpU : p.2 ∈ U := ⟨p, hpK, rfl⟩
    simp only [Set.indicator_of_mem hpX, Set.indicator_of_mem hpU]
    ring

/-- Every parameter section of the compact normal kernel with an almost
everywhere bounded measurable coefficient is integrable
(`app:ch_osc:eq:two-position-normal-bound`). -/
theorem integrable_fullNormalAmplitudeKernel_section
    (t : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) → ℂ)
    (ht : ContDiff ℝ ∞ (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t))
    (g : Lp ℂ ∞ (volume.restrict D))
    (b : EuclideanSpace ℝ (Fin m) → ℂ)
    (hb : AEStronglyMeasurable b (volume.restrict D))
    {B : ℝ} (hB : ∀ᵐ u ∂volume.restrict D, ‖b u‖ ≤ B)
    (x y : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun u ↦ t x u * b u * star (t y u) * g u) (volume.restrict D) := by
  let U := Prod.snd '' tsupport (Function.uncurry t)
  have hU : IsCompact U := hs.image continuous_snd
  have hgi : Integrable (U.indicator (g : EuclideanSpace ℝ (Fin m) → ℂ))
      (volume.restrict D) :=
    ((Lp.memLp g).locallyIntegrable (by simp)).integrableOn_isCompact hU
      |>.integrable_indicator hU.measurableSet
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous ht.continuous
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (0, 0))
  have hx : Continuous (t x) := ht.continuous.comp (continuous_const.prodMk continuous_id)
  have hy : Continuous (t y) := ht.continuous.comp (continuous_const.prodMk continuous_id)
  have hbound : ∀ᵐ u ∂volume.restrict D, ‖t x u * b u * star (t y u)‖ ≤ C * |B| * C := by
    filter_upwards [hB] with u hu
    simp only [norm_mul, norm_star]
    gcongr
    · exact hC (x, u)
    · exact hu.trans (le_abs_self B)
    · exact hC (y, u)
  apply (hgi.bdd_mul ((hx.aestronglyMeasurable.mul hb).mul
    hy.star.aestronglyMeasurable) hbound).congr
  apply Eventually.of_forall
  intro u
  by_cases hu : t x u = 0
  · simp [hu]
  · have huU : u ∈ U := ⟨(x, u), subset_tsupport (Function.uncurry t) hu, rfl⟩
    simp only [Set.indicator_of_mem huU]
    rfl

end JanetCartan.AmplitudeBound
