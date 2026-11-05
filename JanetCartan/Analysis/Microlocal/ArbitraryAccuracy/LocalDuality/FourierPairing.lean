module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Basic

/-!
# Weighted Euclidean L² pairing

The whole-space Cauchy–Schwarz step of
`app:ch_regular_base:eq:negative-duality`, consumed by the local pairing in
`app:ch_regular:eq:inverse-remainder`. The weights and transform are the shared
Euclidean ones, with coordinate symbol `2π i ξⱼ`. Both weighted representatives
are required to be in L² before their numerical norms are used.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform

namespace JanetCartan.ArbitraryAccuracy

open Pseudodifferential

variable {n : ℕ}

/-- Opposite Sobolev weights cancel in the pairing
(`app:ch_regular_base:eq:negative-duality`). -/
theorem inner_weightedL2Fourier_neg (s : ℝ)
    (h v : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    inner ℂ (weightedL2Fourier (-s) h ξ) (weightedL2Fourier s v ξ) =
      inner ℂ ((𝓕 h : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2) ξ)
        ((𝓕 v : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2) ξ) := by
  have hw : euclideanSobolevWeight s ξ * euclideanSobolevWeight (-s) ξ = 1 := by
    rw [← euclideanSobolevWeight_add, add_neg_cancel, euclideanSobolevWeight_zero]
  simp only [weightedL2Fourier, inner_smul_left_eq_smul,
    inner_smul_right_eq_smul, smul_smul, hw, one_smul]

/-- Plancherel identifies the actual L² pairing with that of the opposite
weighted representatives (`app:ch_regular_base:eq:negative-duality`). -/
theorem inner_eq_weightedFourier_inner {s : ℝ}
    {h v : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2}
    (hh : MemFourierSobolev (-s) h) (hv : MemFourierSobolev s v) :
    inner ℂ h v = inner ℂ (hh.toLp _) (hv.toLp _) := by
  rw [← Lp.inner_fourier_eq h v, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hh.coeFn_toLp, hv.coeFn_toLp] with ξ hξ vξ
  rw [hξ, vξ, inner_weightedL2Fourier_neg]

/-- Weighted Fourier Cauchy–Schwarz for actual whole-space L² classes,
the analytic pairing step of `app:ch_regular_base:eq:negative-duality`. -/
theorem norm_inner_le_fourierSobolevNorm_mul {s : ℝ}
    {h v : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2}
    (hh : MemFourierSobolev (-s) h) (hv : MemFourierSobolev s v) :
    ‖inner ℂ h v‖ ≤ fourierSobolevNorm (-s) h * fourierSobolevNorm s v := by
  rw [inner_eq_weightedFourier_inner hh hv]
  have hb := norm_inner_le_norm (𝕜 := ℂ) (hh.toLp _) (hv.toLp _)
  rw [Lp.norm_toLp _ hh, Lp.norm_toLp _ hv] at hb
  exact hb

end JanetCartan.ArbitraryAccuracy
