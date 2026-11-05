module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.Algebra
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Compact smooth approximation at order zero

For the endpoint of `app:ch_regular_base:eq:fio-input`, Mathlib's compact smooth
L² approximation gives actual test functions converging to every L² class.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- Compact smooth approximation in L², the zero-order density endpoint of
`app:ch_regular_base:eq:fio-input`. Positive Sobolev orders require a separate
approximation argument controlling the weighted Fourier norm. -/
theorem exists_compactSmooth_L2_tendsto (v : L²) :
    ∃ g : ℕ → E → ℂ, ∃ hg : ∀ k, ContDiff ℝ ∞ (g k),
      ∃ hc : ∀ k, HasCompactSupport (g k),
      Tendsto (fun k ↦ ((hg k).continuous.memLp_of_hasCompactSupport (hc k)).toLp (g k))
        atTop (𝓝 v) := by
  have hex (k : ℕ) := MemLp.exist_eLpNorm_sub_le
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (Lp.memLp v)
    (show (0 : ℝ) < (1 / 2 : ℝ) ^ k by positivity)
  choose g hc hg he using hex
  refine ⟨g, hg, hc, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ ↦ dist_nonneg) _
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  intro k
  rw [dist_comm, Lp.dist_def]
  have hae : (⇑v - ⇑(((hg k).continuous.memLp_of_hasCompactSupport (hc k)).toLp (g k) : L²))
      =ᵐ[volume] (⇑v - g k) := by
    filter_upwards [((hg k).continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) (hc k)).coeFn_toLp]
      with x hx
    simp only [Pi.sub_apply, hx]
  rw [eLpNorm_congr_ae hae]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (he k)

end JanetCartan.Pseudodifferential
