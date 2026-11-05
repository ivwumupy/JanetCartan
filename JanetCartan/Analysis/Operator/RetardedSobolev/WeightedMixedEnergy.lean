module

public import JanetCartan.Analysis.Operator.RetardedSobolev.MixedMultiplication
public import JanetCartan.Analysis.Operator.RetardedSobolev.Smooth

/-!
# Mixed derivative bounds for the weighted retarded operators

The classical nonnegative-order estimate of `app:ch_osc:prop:osc-retarded-tube`.
Every mixed derivative and its L² membership are included. The constant depends
only on the interval, direction family, order, and the two fixed cutoffs.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.RetardedSobolev

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  {ι : Type*} [Fintype ι]

/-- Both concrete weighted integrals satisfy every nonnegative mixed classical
Sobolev bound (`app:ch_osc:prop:osc-retarded-tube`). The common constant is
chosen before the smooth input, and output jet integrability is proved. -/
theorem mixedSobolev_bounds_of_contDiff_hasCompactSupport
    (directions : ι → Y) (ν : Measure Y) [SFinite ν]
    (a b : ℝ) (hab : a ≤ b) (m : ℕ) (χin χout : ℝ × Y → ℝ)
    (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hsin : HasCompactSupport χin) (hsout : HasCompactSupport χout) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ × Y → ℂ, ContDiff ℝ ∞ f →
      MixedJetsMemLp directions ν a b m f →
      MixedJetsMemLp directions ν a b m (Retarded.lower a χin χout f) ∧
      MixedJetsMemLp directions ν a b m (Retarded.upper b χin χout f) ∧
      mixedSobolevEnergy directions ν a b m (Retarded.lower a χin χout f) ≤
        C * mixedSobolevEnergy directions ν a b m f ∧
      mixedSobolevEnergy directions ν a b m (Retarded.upper b χin χout f) ≤
        C * mixedSobolevEnergy directions ν a b m f := by
  let : ProperSpace Y := FiniteDimensional.proper ℝ Y
  obtain ⟨Ci, hCi, hi⟩ := mixedSobolev_mul_bound directions ν a b m χin hin hsin
  obtain ⟨Co, hCo, ho⟩ := mixedSobolev_mul_bound directions ν a b m χout hout hsout
  refine ⟨Co * (1 + (b - a) ^ 2) * Ci, by positivity, ?_⟩
  intro f hfc hf
  have hif := hi f hfc hf
  have hof := ho f hfc hf
  have hic : ContDiff ℝ ∞ (fun x ↦ (χin x : ℂ) * f x) := (Complex.ofRealCLM.contDiff.comp hin).mul hfc
  have hoc : ContDiff ℝ ∞ (fun x ↦ (χout x : ℂ) * f x) := (Complex.ofRealCLM.contDiff.comp hout).mul hfc
  have hl := lower_one_mixedSobolev_bound directions ν a b hab m hic hif.1
  have hu := upper_one_mixedSobolev_bound directions ν a b hab m hoc hof.1
  have hlc := contDiff_lower a (χin := fun _ ↦ 1) (χout := fun _ ↦ 1) contDiff_const contDiff_const hic
  have huc := contDiff_upper b (χin := fun _ ↦ 1) (χout := fun _ ↦ 1) contDiff_const contDiff_const hoc
  have hlo := ho _ hlc hl.1
  have hui := hi _ huc hu.1
  have hel : (fun x ↦ (χout x : ℂ) *
      Retarded.lower a (fun _ ↦ 1) (fun _ ↦ 1) (fun x ↦ (χin x : ℂ) * f x) x) =
      Retarded.lower a χin χout f := by
    funext x
    simp only [Retarded.lower, Complex.ofReal_one, one_mul]
  have heu : (fun x ↦ (χin x : ℂ) *
      Retarded.upper b (fun _ ↦ 1) (fun _ ↦ 1) (fun x ↦ (χout x : ℂ) * f x) x) =
      Retarded.upper b χin χout f := by
    funext x
    simp only [Retarded.upper, Complex.ofReal_one, one_mul]
  rw [hel] at hlo
  rw [heu] at hui
  refine ⟨hlo.1, hui.1, ?_, ?_⟩
  · calc
      _ ≤ Co * ((1 + (b - a) ^ 2) * mixedSobolevEnergy directions ν a b m
          (fun x ↦ (χin x : ℂ) * f x)) :=
        hlo.2.trans (mul_le_mul_of_nonneg_left hl.2 hCo)
      _ ≤ Co * ((1 + (b - a) ^ 2) * (Ci * mixedSobolevEnergy directions ν a b m f)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hif.2 (by positivity)) hCo
      _ = _ := by ring
  · calc
      _ ≤ Ci * ((1 + (b - a) ^ 2) * mixedSobolevEnergy directions ν a b m
          (fun x ↦ (χout x : ℂ) * f x)) :=
        hui.2.trans (mul_le_mul_of_nonneg_left hu.2 hCi)
      _ ≤ Ci * ((1 + (b - a) ^ 2) * (Co * mixedSobolevEnergy directions ν a b m f)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hof.2 (by positivity)) hCi
      _ = _ := by ring

end JanetCartan.RetardedSobolev
