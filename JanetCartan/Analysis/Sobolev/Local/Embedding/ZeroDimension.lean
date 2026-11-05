module

public import JanetCartan.Analysis.Sobolev.Local.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Count
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The zero-dimensional local Sobolev estimate

The local embedding used in `app:ch_regular:thm:exact-correction` also holds
in dimension zero. Euclidean volume is the unit point mass, so every nonzero
finite exponent gives exactly the same norm.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace JanetCartan.LocalSobolev

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- In dimension zero the H¹-to-L⁴ bound has constant one, including for
arbitrary weak restriction-space data (`app:ch_regular:thm:exact-correction`). -/
theorem memLp_four_and_norm_le_restrictionSobolevNorm_zero_dimension
    (c : EuclideanSpace ℝ (Fin 0)) {R : ℝ} (hR : 0 < R)
    {u : LocalL2 (ball c R) F} (hu : MemRestrictionSobolev (ball c R) 1 u) :
    MemLp u 4 (volume.restrict (ball c R)) ∧
      (eLpNorm u 4 (volume.restrict (ball c R))).toReal ≤
        restrictionSobolevNorm (ball c R) 1 u := by
  have hball : ball c R = univ := by
    ext x
    simp [Subsingleton.elim x c, hR]
  have hμ : (volume : Measure (EuclideanSpace ℝ (Fin 0))).restrict (ball c R) =
      Measure.dirac 0 := by
    rw [hball, Measure.restrict_univ, volume_euclideanSpace_eq_dirac]
  constructor
  · simpa only [hμ] using
      (memLp_dirac (p := 4) (f := (u : EuclideanSpace ℝ (Fin 0) → F))
        (a := 0) enorm_lt_top)
  · have heq : eLpNorm u 4 (volume.restrict (ball c R)) =
        eLpNorm u 2 (volume.restrict (ball c R)) := by
      simp [hμ, eLpNorm_dirac, show (4 : ℝ≥0∞) ≠ 0 by norm_num,
        show (2 : ℝ≥0∞) ≠ 0 by norm_num]
    rw [heq, ← Lp.norm_def]
    exact norm_le_restrictionSobolevNorm hu

end JanetCartan.LocalSobolev
