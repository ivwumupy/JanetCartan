module

public import JanetCartan.Iteration.PhysicalMean.CrossIntegral

/-!
# Original annular radial inputs and exact weighted packing

Frequency powers remain in the SAME original input Hilbert space. Packing the
individual annular moments with their original square-root weights commutes
exactly with multiplication by the radial moment on the disjoint shell space.
This identifies the input of each full quadratic derivative branch with the
actual aggregate adjoint moment, without dividing by a sample weight
(`app:ch_mean_pairs:eq:raw-adjoint-moments`, `app:ch_mean_pairs:eq:block-bilinear`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MeasureTheory

namespace JanetCartan.PhysicalMean
open PhysicalSamplingShells RawInputRealization

/-- Every L² input on an ORIGINAL finite annulus has each integer radial
moment. This proves membership only; the sharp quantitative bound still comes
from the aggregate adjoint, never from the annular radius. -/
theorem annular_radial_memLp {n : ℕ} (R : ℝ)
    (f : Lp ℂ 2 (annularMeasure n R)) (k : ℕ) :
    MemLp (fun η ↦ (‖η‖ : ℂ)^k*f η) 2 (annularMeasure n R) := by
  have hc : Continuous (fun η : Euclidean (n-1) ↦ (‖η‖ : ℂ)^k) :=
    (Complex.continuous_ofReal.comp continuous_norm).pow k
  apply (Lp.memLp f).of_le_mul (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (c := (max R 0)^k)
  have hae : ∀ᵐ η ∂annularMeasure n R, η ∈ annulus n R :=
    ae_restrict_mem (measurableSet_annulus n R)
  filter_upwards [hae] with η hη
  have hnorm : ‖η‖ ≤ max R 0 := (by simpa only [Metric.mem_closedBall, dist_zero_right] using hη.1 :
    ‖η‖ ≤ R).trans (le_max_left R 0)
  change ‖(‖η‖ : ℂ)^k*f η‖ ≤ (max R 0)^k*‖f η‖
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg η)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg η) hnorm k) (norm_nonneg _)

variable {n : ℕ} {ι : Type*} [Fintype ι] [MetricSpace ι] [DiscreteTopology ι]
    [MeasurableSpace ι] [BorelSpace ι]
    (radius : ι → ℝ) (weight : ι → ℝ)
    (f : ∀ i, Lp ℂ 2 (annularMeasure n (radius i))) (k : ℕ)
    (hf : ∀ i, MemLp (fun η ↦ (‖η‖ : ℂ)^k*f i η) 2 (annularMeasure n (radius i)))

/-- The actual radial input on each original annulus. -/
def annularRadialInput (i : ι) : Lp ℂ 2 (annularMeasure n (radius i)) :=
  (hf i).toLp (fun η ↦ (‖η‖ : ℂ)^k*f i η)

omit [Fintype ι] [MetricSpace ι] [DiscreteTopology ι] [MeasurableSpace ι] [BorelSpace ι] in
/-- Literal frequency multiplication on each unchanged annular measure. -/
theorem annularRadialInput_ae (i : ι) :
    annularRadialInput radius f k hf i =ᵐ[annularMeasure n (radius i)] fun η ↦ (‖η‖ : ℂ)^k*f i η :=
  (hf i).coeFn_toLp

/-- The original weighted packing and the exact radial moment commute on the
whole disjoint shell measure, including zero-weight labels. -/
theorem weightedAnnularInput_radial_ae :
    weightedAnnularInput radius weight (annularRadialInput radius f k hf) =ᵐ[annularShellMeasure radius]
      fun z ↦ (‖z.2‖ : ℂ)^k*weightedAnnularInput radius weight f z := by
  change ∀ᵐ z ∂Measure.sum (fun i ↦ (annularMeasure n (radius i)).map (Prod.mk i)), _
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  filter_upwards [weightedAnnularInput_ae radius weight (annularRadialInput radius f k hf) i,
    weightedAnnularInput_ae radius weight f i, annularRadialInput_ae radius f k hf i] with η hi hw hr
  rw [hi, hr, hw]
  exact (mul_smul_comm (Real.sqrt (weight i)) ((‖η‖ : ℂ)^k) (f i η)).symm

/-- Genuine membership and exact norm of the actual aggregate radial input.
The only input norm is the one already bounded by the SAME native real
adjoint; no sample-by-sample estimate or input cardinality is introduced. -/
theorem weightedAnnularInput_radial_memLp_norm :
    MemLp (fun z ↦ (‖z.2‖ : ℂ)^k*weightedAnnularInput radius weight f z) 2 (annularShellMeasure radius) ∧
      ‖weightedAnnularInput radius weight (annularRadialInput radius f k hf)‖ =
        lpNorm (fun z ↦ (‖z.2‖ : ℂ)^k*weightedAnnularInput radius weight f z) 2 (annularShellMeasure radius) := by
  have he := weightedAnnularInput_radial_ae radius weight f k hf
  refine ⟨(memLp_congr_ae he).mp (Lp.memLp _), ?_⟩
  rw [Lp.norm_def, ← toReal_eLpNorm, eLpNorm_congr_ae he]

end JanetCartan.PhysicalMean
