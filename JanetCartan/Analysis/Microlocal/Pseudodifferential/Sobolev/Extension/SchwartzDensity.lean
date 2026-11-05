module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.Algebra

/-!
# Schwartz approximation in Fourier Sobolev spaces

For the natural-order extension of `app:ch_regular_base:eq:fio-input`, approximate
an actual L² class in the Fourier Sobolev norm by Schwartz functions. We approximate
its weighted Fourier transform in L², multiply the Schwartz approximants by the
inverse Bessel weight, and apply inverse Fourier. The existing Fourier transform
keeps the manuscript's `2π` convention. Neither the dimension nor the natural
order is assumed positive.

The consuming compact smooth density assembly can then approximate each Schwartz
function by compact smooth functions before extending
`exists_twoPositionL2Operator_integer_tame_constant` and its gain-one counterpart.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology SchwartzMap

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- Schwartz functions belong to the actual Fourier Sobolev space at every real
order. This supplies the membership of the intermediate approximants used in the
compact smooth density step for `app:ch_regular_base:eq:fio-input`. -/
theorem memFourierSobolev_schwartz (s : ℝ) (f : SchwartzMap E ℂ) :
    MemFourierSobolev s (f.toLp 2 volume) := by
  let g := SchwartzMap.smulLeftCLM ℂ (euclideanSobolevWeight s) (𝓕 f)
  change MemLp _ 2 volume
  apply (g.memLp 2 volume).ae_eq
  filter_upwards [(𝓕 f).coeFn_toLp 2] with ξ hξ
  simp only [weightedL2Fourier, SchwartzMap.toLp_fourier_eq, hξ]
  exact SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_euclideanSobolevWeight s) _ _

/-- Cancel the inverse weight after inverse Fourier, identifying the weighted
approximants for the density step in `app:ch_regular_base:eq:fio-input`. -/
private theorem weightedL2Fourier_inverseWeight_fourierInv_ae (s : ℝ) (g : SchwartzMap E ℂ) :
    weightedL2Fourier s
      ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (euclideanSobolevWeight (-s)) g)).toLp 2 volume)
      =ᵐ[volume] g := by
  let h := SchwartzMap.smulLeftCLM ℂ (euclideanSobolevWeight (-s)) g
  filter_upwards [h.coeFn_toLp 2] with ξ hξ
  simp only [weightedL2Fourier, SchwartzMap.toLp_fourier_eq, fourier_fourierInv_eq]
  rw [hξ, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_euclideanSobolevWeight (-s)),
    smul_smul, ← euclideanSobolevWeight_add]
  simp

/-- Every actual L² class of natural Fourier Sobolev order is the limit of Schwartz
functions in that Sobolev norm and in L². This is the Schwartz approximation step
in the compact smooth density assembly for `app:ch_regular_base:eq:fio-input`,
including dimension zero and order zero. -/
theorem exists_schwartz_fourierSobolev_nat_tendsto (n : ℕ) (v : L²) (hv : MemFourierSobolev (n : ℝ) v) :
    ∃ f : ℕ → SchwartzMap E ℂ,
      (∀ k, MemFourierSobolev (n : ℝ) ((f k).toLp 2 volume)) ∧
      Tendsto (fun k ↦ fourierSobolevNorm (n : ℝ) ((f k).toLp 2 volume - v)) atTop (𝓝 0) ∧
      Tendsto (fun k ↦ (f k).toLp 2 volume) atTop (𝓝 v) := by
  let w : L² := hv.toLp (weightedL2Fourier (n : ℝ) v)
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp
    ((SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2)
      (μ := (volume : Measure E)) ENNReal.ofNat_ne_top) w)
  choose g hg using hu
  let f : ℕ → SchwartzMap E ℂ := fun k ↦
    𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (euclideanSobolevWeight (-(n : ℝ))) (g k))
  have hf (k : ℕ) := memFourierSobolev_schwartz (n : ℝ) (f k)
  have heq (k : ℕ) : (hf k).toLp (weightedL2Fourier (n : ℝ) ((f k).toLp 2 volume)) = u k := by
    rw [← hg k]
    exact MemLp.toLp_congr (hf k) ((g k).memLp 2 volume)
      (weightedL2Fourier_inverseWeight_fourierInv_ae (n : ℝ) (g k))
  have hs : Tendsto (fun k ↦ fourierSobolevNorm (n : ℝ) ((f k).toLp 2 volume - v))
      atTop (𝓝 0) := by
    have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp hlim
    simpa only [fourierSobolevNorm_sub_eq_norm (hf _) hv, heq] using hnorm
  exact ⟨f, hf, hs, tendsto_L2_of_fourierSobolevNorm_sub (Nat.cast_nonneg n) hf hv hs⟩

end JanetCartan.Pseudodifferential
