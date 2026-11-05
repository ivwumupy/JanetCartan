module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Basic

/-!
# Physical and unit-period Sobolev weights

Notation `app:ch_osc:defn:osc-fourier` uses the physical derivative `D=-i∂`.
With Mathlib's unitary transform, its Sobolev norm is the L² norm of
`⟨2πξ⟩^m 𝓕f`. The sharp row-amplitude proof uses the smaller unit-period
weight `⟨ξ⟩^m`. This leaf proves the membership and norm implication from
the original physical norm required by `app:ch_osc:eq:amplitude-row`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform

namespace JanetCartan.FourierConventions

open Pseudodifferential

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "H" => Lp ℂ 2 (volume : Measure E)

/-- The physical Bessel weight dominates the unit-period weight at every
natural order (`app:ch_osc:defn:osc-fourier`). -/
theorem euclideanSobolevWeight_le_physical (m : ℕ) (ξ : E) :
    euclideanSobolevWeight (m : ℝ) ξ ≤
      euclideanSobolevWeight (m : ℝ) ((2 * Real.pi) • ξ) := by
  have hn : ‖ξ‖ ≤ ‖(2 * Real.pi) • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have hπ : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
    nlinarith [norm_nonneg ξ]
  apply Real.rpow_le_rpow (by positivity)
  · nlinarith [norm_nonneg ξ, norm_nonneg ((2 * Real.pi) • ξ)]
  · positivity

/-- The paper's physical `H^m` membership and norm supply the original
unit-period Sobolev input of the sharp row-amplitude theorem. The real norm
comparison is made only after weighted L² membership is supplied
(`app:ch_osc:eq:amplitude-row`). -/
theorem fourierSobolev_of_physical_weight (m : ℕ) (f : H)
    (hphys : MemLp (fun ξ ↦
      euclideanSobolevWeight (m : ℝ) ((2 * Real.pi) • ξ) • (𝓕 f : H) ξ) 2 volume) :
    MemFourierSobolev (m : ℝ) f ∧
      fourierSobolevNorm (m : ℝ) f ≤
        (eLpNorm (fun ξ ↦
          euclideanSobolevWeight (m : ℝ) ((2 * Real.pi) • ξ) • (𝓕 f : H) ξ)
          2 volume).toReal := by
  have hb (ξ : E) : ‖weightedL2Fourier (m : ℝ) f ξ‖ ≤
      ‖euclideanSobolevWeight (m : ℝ) ((2 * Real.pi) • ξ) • (𝓕 f : H) ξ‖ := by
    rw [norm_weightedL2Fourier, norm_smul,
      Real.norm_of_nonneg (euclideanSobolevWeight_pos _ _).le]
    exact mul_le_mul_of_nonneg_right (euclideanSobolevWeight_le_physical m ξ)
      (norm_nonneg _)
  have hm := aestronglyMeasurable_weightedL2Fourier (m : ℝ) f
  refine ⟨hphys.mono hm (Filter.Eventually.of_forall hb), ?_⟩
  exact ENNReal.toReal_mono hphys.eLpNorm_ne_top
    (eLpNorm_mono_ae hm (Filter.Eventually.of_forall hb))

end JanetCartan.FourierConventions
