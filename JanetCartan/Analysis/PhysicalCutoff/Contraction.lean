module

public import JanetCartan.Analysis.PhysicalCutoff.Reality

/-!
# Physical L² contraction of the constructed Fourier truncation

Paper-v2 §15, Step 7: Plancherel and the actual `[0,1]` multiplier prove
contraction on the same real Schwartz representative. No support or norm
bound for the output is assumed. The norm is exactly the shared Lebesgue
physical L² norm, not a periodic or renormalized norm.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace JanetCartan.PhysicalCutoff

variable {n N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Complex inclusion preserves the actual physical L² norm (§15, Step 7). -/
theorem norm_complexify_toLp (u : 𝓢(E, V)) :
    ‖(complexify u).toLp 2 volume‖ = PhysicalBernstein.physicalL2Norm u := by
  rw [SchwartzMap.norm_toLp]
  unfold PhysicalBernstein.physicalL2Norm
  congr 1
  exact eLpNorm_congr_norm_ae (complexify u).continuous.aestronglyMeasurable
    u.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x ↦ euclideanComplexInclusion_norm (u x)))

/-- The constructed frequency field contracts pointwise (§15, Step 7). -/
theorem norm_filteredFourier_le (R : ℝ) (u : 𝓢(E, V)) (ξ : E) :
    ‖filteredFourier R u ξ‖ ≤ ‖𝓕 (complexify u) ξ‖ := by
  rw [filteredFourier_apply, norm_smul, Real.norm_of_nonneg (symbol_mem_Icc R ξ).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (symbol_mem_Icc R ξ).2

/-- The actual smooth Fourier multiplier is an L² contraction (§15, Step 7). -/
theorem norm_filteredFourier_toLp_le (R : ℝ) (u : 𝓢(E, V)) :
    ‖(filteredFourier R u).toLp 2 volume‖ ≤ ‖(𝓕 (complexify u)).toLp 2 volume‖ := by
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp]
  apply ENNReal.toReal_mono ((𝓕 (complexify u)).memLp 2 volume).eLpNorm_ne_top
  exact eLpNorm_mono (filteredFourier R u).continuous.aestronglyMeasurable
    (norm_filteredFourier_le R u)

/-- Physical L² contraction for the actual real Schwartz increment
(§15, Step 7). No positivity or output-bound hypothesis is needed. -/
theorem physicalL2Norm_truncate_le (R : ℝ) (u : 𝓢(E, V)) :
    PhysicalBernstein.physicalL2Norm (truncate R u) ≤
      PhysicalBernstein.physicalL2Norm u := by
  rw [← norm_complexify_toLp, complexify_truncate,
    ← SchwartzMap.norm_fourier_toL2_eq (complexTruncate R u), fourier_complexTruncate]
  calc
    ‖(filteredFourier R u).toLp 2 volume‖ ≤ ‖(𝓕 (complexify u)).toLp 2 volume‖ :=
      norm_filteredFourier_toLp_le R u
    _ = PhysicalBernstein.physicalL2Norm u := by
      rw [SchwartzMap.norm_fourier_toL2_eq, norm_complexify_toLp]

/-- The physical norm obeys the triangle inequality for the actual Schwartz
primary and corrector fields (§15, Step 7). Finiteness is proved by Schwartz
membership, rather than inferred from the total raw-field norm. -/
theorem physicalL2Norm_add_le (u v : 𝓢(E, V)) :
    PhysicalBernstein.physicalL2Norm (u + v) ≤
      PhysicalBernstein.physicalL2Norm u + PhysicalBernstein.physicalL2Norm v := by
  simp only [PhysicalBernstein.physicalL2Norm_eq_norm_toLp]
  change ‖SchwartzMap.toLpCLM ℝ V 2 volume (u + v)‖ ≤ _
  rw [map_add]
  exact norm_add_le (u.toLp 2 volume) (v.toLp 2 volume)

/-- The actual truncated increment of the SAME primary/corrector sum has
no larger physical norm than their original sum of norms (§15, Step 7). -/
theorem physicalL2Norm_truncate_add_le (R : ℝ) (u v : 𝓢(E, V)) :
    PhysicalBernstein.physicalL2Norm (truncate R (u + v)) ≤
      PhysicalBernstein.physicalL2Norm u + PhysicalBernstein.physicalL2Norm v :=
  (physicalL2Norm_truncate_le R (u + v)).trans (physicalL2Norm_add_le u v)

end JanetCartan.PhysicalCutoff
