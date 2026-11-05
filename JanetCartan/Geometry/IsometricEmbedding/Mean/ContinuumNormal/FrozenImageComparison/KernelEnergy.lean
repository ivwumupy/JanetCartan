module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

/-!
# The L¹-squared bound for a compact continuous normal kernel

The frozen image comparison in `paper-v2.tex`,
`app:ch_background:prop:bg-frame`, needs a bounded double-kernel estimate.
The bound below is proved from continuity and compact support of the kernel;
the constant is chosen before the input or its support radius. The periodic
and separated-source constructions must still produce their actual kernels
and identify their energy differences with these integrals.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem kernel_pairing_bound (K : E × E → E →L[ℝ] E)
    {C : ℝ} (hK : ∀ p, ‖K p‖ ≤ C) (u : E → E) (x y : E) :
    ‖⟪u x, K (x, y) (u y)⟫‖ ≤ C * ‖u x‖ * ‖u y‖ := by
  calc
    _ ≤ ‖u x‖ * ‖K (x, y) (u y)‖ := norm_inner_le_norm _ _
    _ ≤ ‖u x‖ * (C * ‖u y‖) := mul_le_mul_of_nonneg_left
      ((K (x, y)).le_opNorm (u y) |>.trans
        (mul_le_mul_of_nonneg_right (hK _) (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by ring

/-- A continuous compact kernel supplies an actual, absolutely convergent
double-energy estimate with one constant for all L¹ inputs, hence for all
supported L² zero extensions (`app:ch_background:prop:bg-frame`). No normal
comparison or kernel bound is assumed. -/
theorem exists_compactKernel_energy_bound
    (K : E × E → E →L[ℝ] E) (hK : Continuous K) (hKs : HasCompactSupport K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E → E, Integrable u →
      Integrable (fun p : E × E ↦ ⟪u p.1, K p (u p.2)⟫) (volume.prod volume) ∧
      |∫ x, ∫ y, ⟪u x, K (x, y) (u y)⟫| ≤ C * (∫ x, ‖u x‖) ^ 2 := by
  obtain ⟨B, hB⟩ := hKs.exists_bound_of_continuous hK
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hb : ∀ p, ‖K p‖ ≤ C := fun p ↦ (hB p).trans (le_max_left _ _)
  refine ⟨C, hC, fun u hu ↦ ?_⟩
  have hm : Integrable (fun p : E × E ↦ C * ‖u p.1‖ * ‖u p.2‖)
      (volume.prod volume) := by
    simpa only [mul_assoc] using (hu.norm.mul_prod hu.norm).const_mul C
  have hi : Integrable (fun p : E × E ↦ ⟪u p.1, K p (u p.2)⟫)
      (volume.prod volume) := hm.mono'
    (hu.aestronglyMeasurable.comp_fst.inner
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hK.aestronglyMeasurable.prodMk hu.aestronglyMeasurable.comp_snd)))
    (Filter.Eventually.of_forall fun p ↦ kernel_pairing_bound K hb u p.1 p.2)
  refine ⟨hi, ?_⟩
  have hsection (x : E) :
      ‖∫ y, ⟪u x, K (x, y) (u y)⟫‖ ≤ C * ‖u x‖ * ∫ y, ‖u y‖ := by
    calc
      _ ≤ ∫ y, C * ‖u x‖ * ‖u y‖ := norm_integral_le_of_norm_le
        (hu.norm.const_mul _) (Filter.Eventually.of_forall fun y ↦
          kernel_pairing_bound K hb u x y)
      _ = _ := integral_const_mul _ _
  calc
    _ = ‖∫ x, ∫ y, ⟪u x, K (x, y) (u y)⟫‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, C * ‖u x‖ * ∫ y, ‖u y‖ := norm_integral_le_of_norm_le
      ((hu.norm.const_mul C).mul_const _) (Filter.Eventually.of_forall hsection)
    _ = C * (∫ x, ‖u x‖) ^ 2 := by
      rw [integral_mul_const, integral_const_mul]
      ring

end JanetCartan.ContinuumNormal.FrozenImageComparison
