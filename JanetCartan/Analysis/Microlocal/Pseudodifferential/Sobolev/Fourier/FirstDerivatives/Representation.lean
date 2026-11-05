module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Basic
/-!
# L² representatives of tempered Fourier multipliers

The equivalence with Mathlib's Bessel potential space and the almost everywhere
identification of representatives support the gain-one argument following
`app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap ContDiff

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}

/-- Equality of the multiplied distribution with an L² distribution forces
almost everywhere equality with the pointwise product. This is the
representative-identification step for
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem ae_eq_pointwise_smul_of_toTemperedDistribution_eq
    (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg : g.HasTemperateGrowth)
    (u v : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (h : TemperedDistribution.smulLeftCLM ℂ g
      (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) = v) :
    (fun ξ ↦ g ξ • u ξ) =ᵐ[volume] v := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp u).locallyIntegrable (by norm_num) |>.continuous_smul hg.1.continuous)
    ((Lp.memLp v).locallyIntegrable (by norm_num))
  intro f hf hfc
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ f) := hfc.comp_left rfl
  have hd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ f) := by fun_prop
  have he := congrArg (fun T : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ) ↦
    T (hc.toSchwartzMap hd)) h
  simpa [TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
    Function.comp_def, smul_smul, mul_comm, mul_left_comm, mul_assoc] using he

/-- The actual weighted Fourier L² membership in
`app:ch_regular_base:eq:fio-input` is equivalent to Mathlib's Bessel-potential
membership, at every real order. -/
theorem memFourierSobolev_iff_memSobolev {s : ℝ}
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2} :
    MemFourierSobolev s u ↔
      TemperedDistribution.MemSobolev s 2 (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
  refine ⟨MemFourierSobolev.memSobolev, ?_⟩
  intro h
  obtain ⟨v, hv⟩ := TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier.mp h
  rw [Lp.fourier_toTemperedDistribution_eq] at hv
  have hg : (fun ξ : EuclideanSpace ℝ (Fin d) ↦
      (euclideanSobolevWeight s ξ : ℂ)).HasTemperateGrowth := by
    unfold euclideanSobolevWeight
    fun_prop
  have hae := ae_eq_pointwise_smul_of_toTemperedDistribution_eq _ hg (𝓕 u) v hv
  change MemLp (weightedL2Fourier s u) 2
  apply (Lp.memLp v).ae_eq
  filter_upwards [hae] with ξ hξ
  simpa [weightedL2Fourier] using hξ.symm

end JanetCartan.Pseudodifferential
