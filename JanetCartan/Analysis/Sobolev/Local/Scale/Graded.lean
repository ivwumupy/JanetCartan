module

public import JanetCartan.Analysis.Sobolev.Local.Scale.Algebra
public import JanetCartan.Analysis.Operator.GradedInverse.Scale

/-!
# The integer restriction Sobolev scale

Actual local L² submodules and their restriction seminorms supply the graded
scale used in `app:ch_regular:thm:exact-correction`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set (EuclideanSpace ℝ (Fin n))}

/-- The genuine restriction Sobolev submodule of local L² (`app:not:fourier`). -/
def restrictionSobolevLevel (U : Set (EuclideanSpace ℝ (Fin n))) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (s : ℕ) : Submodule ℝ (LocalL2 U F) where
  carrier := {u | MemRestrictionSobolev U s u}
  zero_mem' := memRestrictionSobolev_zero_element
  add_mem' := fun hu hv ↦ hu.add hv
  smul_mem' := fun c _ hu ↦ hu.smul c

/-- Level membership is exactly existence of a weak Sobolev extension
(`app:not:fourier`). -/
@[simp] theorem mem_restrictionSobolevLevel_iff (s : ℕ) (u : LocalL2 U F) :
    u ∈ restrictionSobolevLevel U F s ↔ MemRestrictionSobolev U s u := Iff.rfl

/-- Level zero is all local L² for a measurable domain (`app:not:fourier`). -/
theorem restrictionSobolevLevel_zero (hU : MeasurableSet U) :
    restrictionSobolevLevel U F 0 = ⊤ := by
  apply top_unique
  intro u _
  exact memRestrictionSobolev_zero hU u

/-- Higher restriction Sobolev levels include into lower ones (`app:not:fourier`). -/
theorem antitone_restrictionSobolevLevel : Antitone (restrictionSobolevLevel U F) :=
  fun _ _ h _ hu ↦ MemRestrictionSobolev.mono hu h

/-- The restriction norm as a seminorm on its actual domain (`app:not:fourier`). -/
def restrictionSobolevSeminorm (U : Set (EuclideanSpace ℝ (Fin n))) (s : ℕ) :
    Seminorm ℝ (restrictionSobolevLevel U F s) where
  toFun u := restrictionSobolevNorm U s u.val
  map_zero' := restrictionSobolevNorm_zero_element
  add_le' u v := restrictionSobolevNorm_add_le u.property v.property
  neg' u := by
    simpa using restrictionSobolevNorm_smul u.property (-1)
  smul' c u := by
    change restrictionSobolevNorm U s (c • u.val) = ‖c‖ * restrictionSobolevNorm U s u.val
    rw [Real.norm_eq_abs]
    exact restrictionSobolevNorm_smul u.property c

/-- Evaluation of the restriction seminorm (`app:not:fourier`). -/
@[simp] theorem restrictionSobolevSeminorm_eq (s : ℕ)
    (u : restrictionSobolevLevel U F s) :
    restrictionSobolevSeminorm U s u = restrictionSobolevNorm U s u.val := rfl

/-- The restriction scale on local L², normalized at order zero
(`app:ch_regular:thm:exact-correction`). -/
def restrictionSobolevScale (U : Set (EuclideanSpace ℝ (Fin n))) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hU : MeasurableSet U) :
    JanetCartan.GradedScale (LocalL2 U F) where
  level := restrictionSobolevLevel U F
  level_zero := restrictionSobolevLevel_zero hU
  antitone_level := antitone_restrictionSobolevLevel
  seminorm := restrictionSobolevSeminorm U
  seminorm_zero u := restrictionSobolevNorm_zero hU u.val
  monotone_seminorm h u := restrictionSobolevNorm_mono u.property h

/-- The scale's grade norm agrees with the actual infimum restriction norm on
its domain (`app:ch_regular:thm:exact-correction`). -/
theorem restrictionSobolevScale_gradeNorm (hU : MeasurableSet U) {s : ℕ}
    {u : LocalL2 U F} (hu : MemRestrictionSobolev U s u) :
    (restrictionSobolevScale U F hU).gradeNorm s u = restrictionSobolevNorm U s u :=
  (restrictionSobolevScale U F hU).gradeNorm_eq hu

end JanetCartan.LocalSobolev
