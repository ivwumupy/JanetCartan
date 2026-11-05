module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.CompactSchwartz
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.SchwartzDensity

/-!
# Compact smooth density at natural Fourier Sobolev orders

For `app:ch_regular_base:eq:fio-input`, combine Schwartz approximation of an
actual Sobolev L² class with compact smooth approximation of each Schwartz
function. Choosing the second error below `2⁻ᵏ` gives convergence in Hⁿ and
in L², including dimension zero and order zero. This supplies the approximation
sequence for `fourierSobolev_operator_bound_of_compactSmooth_nat`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- Every L² class of natural Fourier Sobolev order has compact smooth
approximants converging in that Sobolev norm and in L². This discharges the
density obligation in the extension of `app:ch_regular_base:eq:fio-input`,
with no restriction on the dimension or on the natural order. -/
theorem exists_compactSmooth_fourierSobolev_nat_tendsto
    (n : ℕ) (v : L²) (hv : MemFourierSobolev (n : ℝ) v) :
    ∃ (g : ℕ → E → ℂ) (hg : ∀ k, ContDiff ℝ ∞ (g k))
      (hc : ∀ k, HasCompactSupport (g k)),
      let u : ℕ → L² := fun k ↦
        ((hg k).continuous.memLp_of_hasCompactSupport (hc k)).toLp (g k)
      (∀ k, MemFourierSobolev (n : ℝ) (u k)) ∧
      Tendsto (fun k ↦ fourierSobolevNorm (n : ℝ) (u k - v)) atTop (𝓝 0) ∧
      Tendsto u atTop (𝓝 v) := by
  obtain ⟨f, hf, hlim, _⟩ := exists_schwartz_fourierSobolev_nat_tendsto n v hv
  have happrox (k : ℕ) := exists_compactSmooth_fourierSobolev_error_lt n (f k)
    (show (0 : ℝ) < (1 / 2 : ℝ) ^ k by positivity)
  choose g hg hc he using happrox
  let u : ℕ → L² := fun k ↦
    ((hg k).continuous.memLp_of_hasCompactSupport (hc k)).toLp (g k)
  have hu (k : ℕ) : MemFourierSobolev (n : ℝ) (u k) :=
    memFourierSobolev_nat_toLp n (g k) (hg k) (hc k)
  have hs : Tendsto (fun k ↦ fourierSobolevNorm (n : ℝ) (u k - v)) atTop (𝓝 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    apply squeeze_zero (fun _ ↦ fourierSobolevNorm_nonneg _ _) _
      (show Tendsto (fun k ↦ (1 / 2 : ℝ) ^ k +
        fourierSobolevNorm (n : ℝ) ((f k).toLp 2 volume - v)) atTop (𝓝 0) by
          simpa using hpow.add hlim)
    intro k
    calc
      fourierSobolevNorm (n : ℝ) (u k - v) =
          fourierSobolevNorm (n : ℝ)
            ((u k - (f k).toLp 2 volume) + ((f k).toLp 2 volume - v)) := by
              congr 1
              abel
      _ ≤ fourierSobolevNorm (n : ℝ) (u k - (f k).toLp 2 volume) +
          fourierSobolevNorm (n : ℝ) ((f k).toLp 2 volume - v) :=
        fourierSobolevNorm_add_le ((hu k).sub (hf k)) ((hf k).sub hv)
      _ ≤ (1 / 2 : ℝ) ^ k + fourierSobolevNorm (n : ℝ) ((f k).toLp 2 volume - v) :=
        add_le_add (he k).le le_rfl
  exact ⟨g, hg, hc, hu, hs,
    tendsto_L2_of_fourierSobolevNorm_sub (Nat.cast_nonneg n) hu hv hs⟩

end JanetCartan.Pseudodifferential
