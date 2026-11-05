module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.Basic

/-!
# Sobolev differences and convergence

The approximation step for `app:ch_regular_base:eq:fio-input` uses differences
of actual L² classes. These lemmas identify their weighted norm with an L²
norm and show that Sobolev approximation implies convergence of the norms.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- Weighted Fourier representatives respect subtraction, as needed for the
compact-test approximation in `app:ch_regular_base:eq:fio-input`. -/
theorem weightedL2Fourier_sub_ae (s : ℝ) (u v : L²) :
    weightedL2Fourier s (u - v) =ᵐ[volume]
      fun ξ ↦ weightedL2Fourier s u ξ - weightedL2Fourier s v ξ := by
  have h : 𝓕 (u - v) = 𝓕 u - 𝓕 v := (fourierCLM ℂ L²).map_sub u v
  filter_upwards [Lp.coeFn_sub (𝓕 u) (𝓕 v)] with ξ hξ
  simp only [weightedL2Fourier, h, hξ, Pi.sub_apply, smul_sub]

/-- Sobolev membership of approximation errors for
`app:ch_regular_base:eq:fio-input`. -/
theorem MemFourierSobolev.sub {s : ℝ} {u v : L²}
    (hu : MemFourierSobolev s u) (hv : MemFourierSobolev s v) :
    MemFourierSobolev s (u - v) :=
  (MemLp.sub hu hv).ae_eq (weightedL2Fourier_sub_ae s u v).symm

/-- The Sobolev error is exactly the distance between weighted Fourier L²
classes, for the density step in `app:ch_regular_base:eq:fio-input`. -/
theorem fourierSobolevNorm_sub_eq_norm {s : ℝ} {u v : L²}
    (hu : MemFourierSobolev s u) (hv : MemFourierSobolev s v) :
    fourierSobolevNorm s (u - v) =
      ‖hu.toLp (weightedL2Fourier s u) - hv.toLp (weightedL2Fourier s v)‖ := by
  rw [← MemLp.toLp_sub hu hv, Lp.norm_toLp]
  unfold fourierSobolevNorm
  congr 1
  exact eLpNorm_congr_ae (weightedL2Fourier_sub_ae s u v)

/-- Reverse triangle inequality for the finite Sobolev norms used to preserve
the constant in `app:ch_regular_base:eq:fio-input` under approximation. -/
theorem abs_fourierSobolevNorm_sub_le {s : ℝ} {u v : L²}
    (hu : MemFourierSobolev s u) (hv : MemFourierSobolev s v) :
    |fourierSobolevNorm s u - fourierSobolevNorm s v| ≤
      fourierSobolevNorm s (u - v) := by
  rw [fourierSobolevNorm_sub_eq_norm hu hv]
  simpa only [Lp.norm_toLp _ hu, Lp.norm_toLp _ hv, fourierSobolevNorm] using
    abs_norm_sub_norm_le (hu.toLp (weightedL2Fourier s u))
      (hv.toLp (weightedL2Fourier s v))

/-- Sobolev approximation implies convergence of the numerical norms, for
passing the exact right-hand side of `app:ch_regular_base:eq:fio-input`. -/
theorem tendsto_fourierSobolevNorm_of_sub {s : ℝ} {u : ℕ → L²} {v : L²}
    (hu : ∀ k, MemFourierSobolev s (u k)) (hv : MemFourierSobolev s v)
    (hlim : Tendsto (fun k ↦ fourierSobolevNorm s (u k - v)) atTop (𝓝 0)) :
    Tendsto (fun k ↦ fourierSobolevNorm s (u k)) atTop (𝓝 (fourierSobolevNorm s v)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hlim
  intro k
  simpa only [Real.dist_eq] using abs_fourierSobolevNorm_sub_le (hu k) hv

/-- Nonnegative-order Sobolev approximation also converges in L², as required
by the actual bounded operator in `app:ch_regular_base:eq:fio-input`. -/
theorem tendsto_L2_of_fourierSobolevNorm_sub {s : ℝ} (hs : 0 ≤ s)
    {u : ℕ → L²} {v : L²} (hu : ∀ k, MemFourierSobolev s (u k))
    (hv : MemFourierSobolev s v)
    (hlim : Tendsto (fun k ↦ fourierSobolevNorm s (u k - v)) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 v) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hlim
  intro k
  simpa only [dist_eq_norm] using norm_le_fourierSobolevNorm hs ((hu k).sub hv)

end JanetCartan.Pseudodifferential
