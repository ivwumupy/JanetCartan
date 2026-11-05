module

public import JanetCartan.Iteration.PhysicalSamplingShells.Samples
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Genuine input moment membership on the original shell measure

All input-frequency moments of an arbitrary native sampled L² datum belong to
L² because its ORIGINAL finitely many annuli have bounded radii. This leaf proves
MEMBERSHIP ONLY: the finite ceiling is never inserted into the quantitative
forward estimate. The sharp actual moment norms remain the mean14 outputs.
Square-root sample weights and frequency halfweights remain in the original
kernel and are not moved into the measure.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
namespace JanetCartan.PhysicalForwardMean
open PhysicalSamplingShells RawInputRealization RawInputPartition

variable {n : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Arbitrary L² data on the literal original finite annular union have all
radial input moments in L². No cutoff-size norm estimate is asserted or used
(`app:ch_mean_pairs:eq:block-normal`). -/
theorem memLp_radialMoment_annularShell
    (radius : ι → ℝ) (v : Lp ℂ 2 (annularShellMeasure (n := n) radius)) (k : ℕ) :
    MemLp (fun u : ι × Euclidean (n - 1) ↦ (‖u.2‖ : ℂ)^k * v u) 2
      (annularShellMeasure radius) := by
  classical
  let C := ∑ i, |radius i|
  have hC (i : ι) : radius i ≤ C := (le_abs_self _).trans
    (Finset.single_le_sum (fun i _ ↦ abs_nonneg (radius i)) (Finset.mem_univ i))
  have hn : ∀ᵐ u ∂annularShellMeasure (n := n) radius, ‖u.2‖ ≤ C := by
    apply Measure.ae_sum_iff.mpr
    intro i
    apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
    filter_upwards [ae_restrict_mem (measurableSet_annulus n (radius i))] with η hη
    have hηnorm : ‖η‖ ≤ radius i := by simpa only [Metric.mem_closedBall, dist_zero_right] using hη.1
    exact hηnorm.trans (hC i)
  have hp : MemLp (fun u : ι × Euclidean (n - 1) ↦ (‖u.2‖ : ℂ)^k) (⊤ : ENNReal)
      (annularShellMeasure radius) := by
    apply memLp_top_of_bound
      (((Complex.continuous_ofReal.comp continuous_norm).measurable.comp measurable_snd).pow_const k).aestronglyMeasurable
      (C ^ k)
    filter_upwards [hn] with u hu
    simpa only [Function.comp_def, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_norm] using
      pow_le_pow_left₀ (norm_nonneg u.2) hu k
  exact hp.fun_mul (Lp.memLp v)

/-- The exact `sampledShellMeasure` of the original sample/shell input satisfies
all moment-membership prerequisites of the forward derivative theorem, for
EVERY native input, without an additional regularity assumption. -/
theorem memLp_radialMoment_sampledShell (J : ℕ)
    (v : Lp ℂ 2 (sampledShellMeasure (ι := ι) n J)) (k : ℕ) :
    MemLp (fun u : (ι × RefinedIndex J) × Euclidean (n - 1) ↦ (‖u.2‖ : ℂ)^k * v u) 2
      (sampledShellMeasure (ι := ι) n J) :=
  memLp_radialMoment_annularShell (fun i : ι × RefinedIndex J ↦ refinedRadius i.2) v k

end JanetCartan.PhysicalForwardMean
