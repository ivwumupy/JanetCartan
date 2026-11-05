module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.CompactSchwartz.Cutoff

/-!
# Compact smooth approximation of Schwartz functions in Fourier Sobolev norm

For `app:ch_regular_base:eq:fio-input`, expanding smooth cutoffs approximate
Schwartz data in the actual Fourier Hⁿ norm. The cutoff convergence is proved
in Schwartz topology; the Fourier transform, the manuscript's Bessel weight,
and the map to L² are continuous. This preserves Mathlib's 2π convention and
includes dimension zero and Sobolev order zero.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Filter
open scoped ENNReal SchwartzMap Topology ContDiff

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private def weightedSchwartz (s : ℝ) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (euclideanSobolevWeight s) (𝓕 f)

private theorem norm_weightedSchwartz (s : ℝ) (f : 𝓢(E, ℂ)) :
    fourierSobolevNorm s (f.toLp 2 volume) = ‖(weightedSchwartz s f).toLp 2 volume‖ := by
  rw [SchwartzMap.norm_toLp]
  unfold fourierSobolevNorm
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [(𝓕 f).coeFn_toLp 2 volume] with x hx
  simp only [weightedL2Fourier, f.toLp_fourier_eq, hx, weightedSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_euclideanSobolevWeight s)]

private theorem continuous_schwartz_sobolev_norm (s : ℝ) :
    Continuous (fun f : 𝓢(E, ℂ) ↦ fourierSobolevNorm s (f.toLp 2 volume)) := by
  simp_rw [norm_weightedSchwartz]
  exact (SchwartzMap.continuous_toLp.comp
    ((SchwartzMap.smulLeftCLM ℂ (euclideanSobolevWeight (d := d) s)).continuous.comp
      continuous_fourier)).norm

/-- The explicit expanding compact truncations converge in the actual Fourier
Hⁿ norm, for the compact-test extension in `app:ch_regular_base:eq:fio-input`. -/
theorem tendsto_fourierSobolevNorm_compactSchwartz (n : ℕ) (f : 𝓢(E, ℂ)) :
    Tendsto (fun j ↦ fourierSobolevNorm (n : ℝ)
      ((CompactSchwartz.truncate f j).toLp 2 volume - f.toLp 2 volume)) atTop (𝓝 0) := by
  have hsub : Tendsto (fun j ↦ CompactSchwartz.truncate f j - f) atTop
      (𝓝 (0 : 𝓢(E, ℂ))) := by
    simpa using (CompactSchwartz.tendsto_truncate f).sub_const f
  have ht := ((continuous_schwartz_sobolev_norm (d := d) n).tendsto 0).comp hsub
  have hz : fourierSobolevNorm (n : ℝ) ((0 : 𝓢(E, ℂ)).toLp 2 volume) = 0 := by
    rw [norm_weightedSchwartz]
    simp [weightedSchwartz, SchwartzMap.toLp, MemLp.toLp_zero]
  rw [hz] at ht
  convert ht using 1
  funext j
  congr 1

/-- Compact smooth functions approximate every Schwartz function in the actual
Fourier Hⁿ norm, as required for `app:ch_regular_base:eq:fio-input`. No density
or derivative-convergence premise is assumed; both zero dimension and zero
order are included. -/
theorem exists_compactSmooth_fourierSobolev_approximation (n : ℕ) (f : 𝓢(E, ℂ)) :
    ∃ (g : ℕ → E → ℂ) (hg : ∀ j, ContDiff ℝ ∞ (g j))
      (hc : ∀ j, HasCompactSupport (g j)),
      Tendsto (fun j ↦ fourierSobolevNorm (n : ℝ)
        (((hg j).continuous.memLp_of_hasCompactSupport (hc j)).toLp (g j) - f.toLp 2 volume))
        atTop (𝓝 0) := by
  refine ⟨fun j ↦ CompactSchwartz.truncate f j,
    fun j ↦ (CompactSchwartz.truncate f j).smooth ⊤,
    CompactSchwartz.truncate_hasCompactSupport f, ?_⟩
  exact tendsto_fourierSobolevNorm_compactSchwartz n f

/-- Epsilon form of compact smooth approximation of Schwartz data, consumed
by the natural-order density assembly for `app:ch_regular_base:eq:fio-input`. -/
theorem exists_compactSmooth_fourierSobolev_error_lt (n : ℕ) (f : 𝓢(E, ℂ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : E → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g),
      fourierSobolevNorm (n : ℝ)
        ((hg.continuous.memLp_of_hasCompactSupport hc).toLp g - f.toLp 2 volume) < ε := by
  obtain ⟨g, hg, hc, hlim⟩ := exists_compactSmooth_fourierSobolev_approximation n f
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact ⟨g j, hg j, hc j, hj⟩

end JanetCartan.Pseudodifferential
