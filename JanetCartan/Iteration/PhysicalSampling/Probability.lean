module

public import JanetCartan.Iteration.PhysicalSampling.CommonEvent
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.AsymptoticRealization
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampleBudgets

/-!
# The two-row probability budget at the literal revised sampling scales

The measured and half-weighted scalar rows use one original shift space. Their
two failure probabilities are summed without duplicating any sample label.
The numerical budget is chosen from fixed primitive kernel bounds, before the
current data. The literal revised input ceiling is `T ^ fineExponent`, not the
final output ceiling `T ^ bandExponent`.
Consumers: `app:ch_waves:thm:sampling` and `new:eq:amplitude-test`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace JanetCartan.PhysicalSampling

open Sampling Sampling.AsymptoticRealization Sampling.Realization SeparatedSampling
open SamplingKernelBounds RawInputPartition LatticeQuadrature Sampling.BackgroundQuadrature

/-- The generic cutoff-variable sampling slack must be `1/43` at the original
fine ceiling. Substituting the stage slack `1/32` here would change the mesh and
violate the original sample-count exponent. -/
theorem fineExponent_sampling_parameter :
    fineExponent * (1 + (1 : ℝ) / 43) = 1 + samplingSlack ∧
    fineExponent * ((1 : ℝ) / 43) / 4 = (3 : ℝ) / 512 := by
  norm_num [fineExponent, meanSlack, samplingSlack]

/-- Exact original physical mesh after the fine-ceiling substitution. -/
theorem samplingMesh_fineExponent {T : ℝ} (hT : 0 ≤ T) :
    samplingMesh ((1 : ℝ) / 43) (T ^ fineExponent) = T ^ (-separationExponent) := by
  rw [samplingMesh, ← Real.rpow_mul hT]
  congr 1
  norm_num [fineExponent, meanSlack, separationExponent]

/-- Exact original tolerance `T^(-omega)` with `omega=3/512`. -/
theorem samplingTolerance_fineExponent {T : ℝ} (hT : 0 ≤ T) :
    samplingTolerance ((1 : ℝ) / 43) (T ^ fineExponent) = T ^ (-((3 : ℝ) / 512)) := by
  rw [samplingTolerance, ← Real.rpow_mul hT]
  congr 1
  norm_num [fineExponent, meanSlack]

/-- Counting on the literal same sample space at the fine input ceiling keeps
the original `T^(1+samplingSlack)` count, not a larger rounded-frequency power. -/
theorem sampleIndex_card_le_fine_samplingMesh {A : Type*} [Fintype A]
    (p : ℕ) {B : ℝ} (hB : 0 ≤ B) (ψ : A → Point → ℝ) (w : ℝ → ℝ)
    {T : ℝ} (hT : 1 ≤ T) (U : A → Lattice → Point) :
    (Fintype.card (CanonicalRowComparison.SampleIndex p B ψ w
      (samplingMesh ((1 : ℝ) / 43) (T ^ fineExponent)) U) : ℝ) ≤
        ((Fintype.card A : ℝ) * countConstant p B) * T ^ (1 + samplingSlack) := by
  rw [samplingMesh_fineExponent (zero_le_one.trans hT)]
  exact UniformStep.sampleIndex_card_le_originalScale p hB ψ w hT U

/-- A uniform numerical budget for the SAME measured/scalar sampling event.
There is no assumed tail smallness: both literal tails are proved jointly less
than one from the original primitive kernel constants. The threshold precedes
both rows, hence every admissible current history and inverse frequency. -/
theorem exists_original_common_bernstein_budget
    {A : Type*} [Fintype A] {n p : ℕ}
    {ψ : A → Point → ℝ} {B C_op Cmean ε : ℝ} {P Q : A → ℝ}
    (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hQ : ∀ a, 0 ≤ Q a)
    (hC_op : 0 ≤ C_op) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), Cmean ≤ C ∧
    ∃ Λ₀ ≥ (1 : ℝ), ∀ Λ ≥ Λ₀,
      let R := blockConstant p P C_op * (Λ * samplingMesh ε Λ ^ 3)
      let t := samplingTolerance ε Λ
      0 < R ∧ 0 < t ∧ R * C + R * t / 3 ≤ t ^ 2 ∧
      ∀ D Dscalar : A → BandKernelData
        (Fin (cutoffCount Λ) × ((Fin 3 → Fin (p + 1)) × Point)) n,
        (∀ a, (D a).squaredKernelConstant ≤ Q a) →
        (∀ a, (Dscalar a).squaredKernelConstant ≤ Q a) →
        (cutoffCount Λ + 1 : ENNReal) * OperatorCompression.bernsteinTail R (R * C)
          (R * traceBound D B P) t +
        (cutoffCount Λ + 1 : ENNReal) * OperatorCompression.bernsteinTail R (R * C)
          (R * traceBound Dscalar B P) t < 1 := by
  let α := blockConstant p P C_op
  let C := meanConstant n p B P Q Cmean
  have hα : 0 < α := blockConstant_pos hψ hC_op
  have hC : 0 < C := (meanConstant_bounds hψ hQ).1
  have hmean : Cmean ≤ C := (meanConstant_bounds hψ hQ).2
  obtain ⟨c, hc, hscale⟩ := eventually_sampling_bernstein_scale hα hC hε
  have hdecay := ENNReal.tendsto_ofReal (tendsto_sampling_failure_bound 112 c ε n hc hε)
  simp only [ENNReal.ofReal_zero] at hdecay
  have hsmall : ∀ᶠ Λ : ℝ in atTop,
      ENNReal.ofReal (112 * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2))) < 1 :=
    (tendsto_order.mp hdecay).2 1 (by simp)
  have hevent : ∀ᶠ Λ : ℝ in atTop,
      1 ≤ Λ ∧
      let R := α * (Λ * samplingMesh ε Λ ^ 3)
      let t := samplingTolerance ε Λ
      0 < R ∧ 0 < t ∧ R * C + R * t / 3 ≤ t ^ 2 ∧
      ∀ D Dscalar : A → BandKernelData
        (Fin (cutoffCount Λ) × ((Fin 3 → Fin (p + 1)) × Point)) n,
        (∀ a, (D a).squaredKernelConstant ≤ Q a) →
        (∀ a, (Dscalar a).squaredKernelConstant ≤ Q a) →
        (cutoffCount Λ + 1 : ENNReal) * OperatorCompression.bernsteinTail R (R * C)
          (R * traceBound D B P) t +
        (cutoffCount Λ + 1 : ENNReal) * OperatorCompression.bernsteinTail R (R * C)
          (R * traceBound Dscalar B P) t < 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hscale, hsmall] with Λ hΛ hs hsmall
    let R := α * (Λ * samplingMesh ε Λ ^ 3)
    let t := samplingTolerance ε Λ
    have hR : 0 < R := by
      have hΛpos := zero_lt_one.trans_le hΛ
      have hh : 0 < samplingMesh ε Λ := Real.rpow_pos_of_pos hΛpos _
      dsimp [R]
      positivity
    change 0 < t ∧ 0 < C * R ∧ C * R + R * t / 3 ≤ t ^ 2 ∧
      c * Λ ^ (ε / 2) ≤ t ^ 2 / (2 * (C * R + R * t / 3)) at hs
    rw [mul_comm C R] at hs
    refine ⟨hΛ, hR, hs.1, hs.2.2.1, ?_⟩
    intro D Dscalar hkernel hkernelScalar
    have htrace := (traceBound_bounds (C_mean := Cmean) hΛ D hψ hQ hkernel).2
    have htraceScalar := (traceBound_bounds (C_mean := Cmean) hΛ Dscalar hψ hQ hkernelScalar).2
    have htail := cutoff_bernsteinTail_le hΛ hR hC htrace hs.2.2.2
    have htailScalar := cutoff_bernsteinTail_le hΛ hR hC htraceScalar hs.2.2.2
    calc
      _ ≤ ENNReal.ofReal (56 * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2))) +
          ENNReal.ofReal (56 * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2))) :=
        add_le_add htail htailScalar
      _ = ENNReal.ofReal (112 * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ < 1 := hsmall
  obtain ⟨Λ₀, hΛ₀⟩ := eventually_atTop.mp hevent
  refine ⟨C, hC, hmean, max 1 Λ₀, le_max_left _ _, ?_⟩
  intro Λ hΛ
  exact (hΛ₀ Λ ((le_max_right _ _).trans hΛ)).2

end JanetCartan.PhysicalSampling
