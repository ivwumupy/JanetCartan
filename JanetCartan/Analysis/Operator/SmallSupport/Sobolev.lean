module

public import JanetCartan.Analysis.Operator.SmallSupport.Holder
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-!
# The Sobolev input to small-support localization

For `app:ch_regular:thm:exact-correction` of `paper.tex`, Mathlib's whole-space
Gagliardo–Nirenberg–Sobolev inequality supplies an Lᵖ estimate for compactly
supported C¹ representatives. The lemmas below require an actual representative;
they do not assert an extension theorem for local H¹ functions. In particular,
using these lemmas for the manuscript's residual still requires its uniform
one-derivative bound and a justified extension/density argument.
-/

@[expose] public noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Module
open scoped ENNReal NNReal

namespace JanetCartan.SmallSupport

/-- In dimension above two, the Sobolev exponent is strictly above two,
as required in `app:ch_regular:thm:exact-correction`. -/
theorem exists_sobolev_exponent {n : ℕ} (hn : 2 < n) :
    ∃ p : ℝ≥0, 2 < p ∧ (p : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
  have hn' : (2 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) - 2 := by linarith
  refine ⟨⟨2 * n / (n - 2), by positivity⟩, ?_, ?_⟩
  · change (2 : ℝ) < 2 * n / (n - 2)
    apply (lt_div_iff₀ hd).mpr
    linarith
  · change (2 * (n : ℝ) / (n - 2))⁻¹ = _
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    field_simp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {μ : Measure E} [IsAddHaarMeasure μ]

/-- The available Sobolev inequality bounds the local Lᵖ norm when an actual
compactly supported C¹ representative is supplied. This is the Sobolev input to
`app:ch_regular:thm:exact-correction`, with no implicit local extension. -/
theorem eLpNorm_le_of_compactRepresentative {U : Set E} {g u : E → F}
    (hu : ContDiff ℝ 1 u) (hcompact : HasCompactSupport u)
    (heq : g =ᵐ[μ.restrict U] u) {q p : ℝ≥0} (hq : 1 ≤ q)
    (hn : 0 < finrank ℝ E)
    (hp : (p : ℝ)⁻¹ = (q : ℝ)⁻¹ - (finrank ℝ E : ℝ)⁻¹) :
    eLpNorm g p (μ.restrict U) ≤
      SNormLESNormFDerivOfEqConst F μ q * eLpNorm (fderiv ℝ u) q μ := by
  rw [eLpNorm_congr_ae heq]
  exact (eLpNorm_restrict_le u p μ U).trans
    (eLpNorm_le_eLpNorm_fderiv_of_eq μ hu hcompact hq hn hp)

/-- A quantitative derivative estimate for a supplied whole-space representative
implies the L²-to-Lᵖ estimate needed in `app:ch_regular:thm:exact-correction`.
The exponent identity with `q = 2` is the usual Sobolev exponent in dimension
strictly above two. The more general representative lemma also permits `q < 2`. -/
theorem eLpNorm_le_of_representative_derivative_bound {U : Set E} {g u : E → F}
    (hu : ContDiff ℝ 1 u) (hcompact : HasCompactSupport u)
    (heq : g =ᵐ[μ.restrict U] u) {p : ℝ≥0}
    (hn : 0 < finrank ℝ E)
    (hp : (p : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (finrank ℝ E : ℝ)⁻¹)
    {D : ℝ≥0} {M : ℝ≥0∞}
    (hderiv : eLpNorm (fderiv ℝ u) 2 μ ≤ D * M) :
    eLpNorm g p (μ.restrict U) ≤ (SNormLESNormFDerivOfEqConst F μ 2 * D) * M := by
  calc
    _ ≤ SNormLESNormFDerivOfEqConst F μ 2 * eLpNorm (fderiv ℝ u) 2 μ :=
      eLpNorm_le_of_compactRepresentative hu hcompact heq (q := 2) (by norm_num) hn hp
    _ ≤ SNormLESNormFDerivOfEqConst F μ 2 * (D * M) := by gcongr
    _ = _ := by simp only [mul_assoc]

/-- Combining the actual Sobolev inequality and Hölder gives a support gain for
a localized compactly supported C¹ function (`app:ch_regular:thm:exact-correction`).
No local extension is used in this whole-space statement. -/
theorem eLpNorm_cutoff_le_sobolev {u : E → F} {χ : E → ℝ} {s : Set E}
    (hu : ContDiff ℝ 1 u) (hcompact : HasCompactSupport u)
    (hχ : AEStronglyMeasurable χ μ) (hbound : ∀ x, ‖χ x‖ ≤ 1)
    (hsupport : Function.support χ ⊆ s) {p : ℝ≥0} (hp : 2 < p)
    (hn : 0 < finrank ℝ E)
    (hexp : (p : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (finrank ℝ E : ℝ)⁻¹) :
    eLpNorm (fun x ↦ χ x • u x) 2 μ ≤
      (μ s) ^ (1 / 2 - 1 / (p : ℝ)) *
        (SNormLESNormFDerivOfEqConst F μ 2 * eLpNorm (fderiv ℝ u) 2 μ) := by
  exact (eLpNorm_cutoff_le hp.le hχ hu.continuous.aestronglyMeasurable hbound hsupport).trans
    (mul_le_mul_right (eLpNorm_le_eLpNorm_fderiv_of_eq μ hu hcompact (p := 2) (by norm_num) hn hexp) _)

end JanetCartan.SmallSupport
