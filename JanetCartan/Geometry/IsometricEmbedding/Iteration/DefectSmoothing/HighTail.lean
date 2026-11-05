module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.ExtensionBounds
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.HighProfile

/-!
# The high tail of the actual history defect

For `main:eq:smoothing-high`, the same extension and cutoff used in the small
estimate are applied to the actual profile derived from finite-history budgets.
The dilation interval and constants precede every later scale and history.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan.DefectSmoothing

variable {n : ℕ}

/-- `main:eq:smoothing-high`: the concrete extension and cutoff give a tail
from the core norm at exactly order `N`. No tail is an input. -/
theorem exists_smoothTensor_high_tail_bound (D : LocalDomain) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ f : MetricField n,
      ContDiffOn ℝ ∞ f (D.chart n) →
      cNorm (D.core n) 0 (f - periodicLift (smoothTensor D R f)) ≤
        C * (R ^ N)⁻¹ * cNorm (D.core n) N f := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_extendToTorus_le (n := n) D N
  refine ⟨periodicCutoffApproximationConstant n N * C,
    mul_nonneg (periodicCutoffApproximationConstant_nonneg _ _) hC, ?_⟩
  intro R hR f hf
  have hA := periodicCutoffApproximationConstant_nonneg n N
  have hfN := cNorm_nonneg (D.core n) N f
  have hsmooth := isSmoothPeriodic_extendToTorus D
    (hf.mono (Metric.closedBall_subset_ball D.coreRadius_lt_chartRadius))
  rw [cNorm_order_zero]
  apply Real.sSup_le _ (by positivity)
  rintro _ ⟨x, hx, rfl⟩
  change ‖f x - periodicLift (smoothTensor D R f) x‖ ≤ _
  rw [← periodicLift_extendToTorus_eqOn D f hx]
  calc
    _ ≤ periodicCutoffApproximationConstant n N * (R ^ N)⁻¹ *
        cNorm (fundamentalCell n) N (periodicLift (extendToTorus D f)) :=
      norm_periodicLift_sub_periodicCutoff_le hsmooth N hR x
    _ ≤ periodicCutoffApproximationConstant n N * (R ^ N)⁻¹ *
        (C * cNorm (D.core n) N f) :=
      mul_le_mul_of_nonneg_left (hb f hf) (by positivity)
    _ = _ := by ring

/-- `main:eq:smoothing-high` for the locally smooth normalized target and
actual admissible finite history. The high profile and target dilation estimates
are instantiated, with no high-defect or tail hypothesis. The range conclusion
also supplies the local smoothness needed by the low and normalized bounds. -/
theorem exists_history_high_tail_bound
    (D : LocalDomain) (G : FlatReference n) {ρ : ℝ} (hρ : 0 < ρ)
    {g : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (h0 : (0 : Euclidean n) ∈ U) (hg : ContDiffOn ℝ ∞ g U) (hg0 : g 0 = 1)
    {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (1 + (n : ℝ) / 2) + 2 < kMin) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
      (∀ s ∈ Icc (0 : ℝ) s₀, ∀ x ∈ D.closureChart n, (s * ρ) • x ∈ U) ∧
      ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧
        ∀ s ∈ Icc (0 : ℝ) s₀, ∀ R₀ : ℝ, 2 ≤ R₀ →
          ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
            (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
            ∀ N, let R := iterationScale R₀ growthExponent j
              cNorm (D.core n) 0
                (historyDefect (fun x ↦ g ((s * ρ) • x)) G.map u -
                  periodicLift (smoothedHistoryDefect D R
                    (fun x ↦ g ((s * ρ) • x)) G.map u)) ≤
                C N * (R ^ coefficientExponent / R) ^ N := by
  obtain ⟨s₀, hs₀, hs₁, hmaps, P, hP, hp⟩ :=
    exists_historyDefect_derivative_profile D G hρ hU h0 hg hg0 horder
  choose B hB hb using fun N ↦ exists_smoothTensor_high_tail_bound (n := n) D N
  refine ⟨s₀, hs₀, hs₁, hmaps, fun N ↦ B N * P N,
    fun N ↦ mul_nonneg (hB N) (hP N), ?_⟩
  intro s hs R₀ hR₀ j u ell hu N
  let R := iterationScale R₀ growthExponent j
  have hR : 0 < R := Real.rpow_pos_of_pos (by linarith) _
  have ht : ContDiffOn ℝ ∞ (fun x ↦ g ((s * ρ) • x)) (D.chart n) :=
    hg.comp (contDiff_id.const_smul (s * ρ)).contDiffOn
      (fun x hx ↦ hmaps s hs x (Metric.ball_subset_closedBall hx))
  have he := contDiffOn_historyDefect ht G.contDiff hu
  have hBN := hB N
  calc
    _ ≤ B N * (R ^ N)⁻¹ * cNorm (D.core n) N
        (historyDefect (fun x ↦ g ((s * ρ) • x)) G.map u) := hb N R hR _ he
    _ ≤ B N * (R ^ N)⁻¹ * (P N * (R ^ coefficientExponent) ^ N) :=
      mul_le_mul_of_nonneg_left (hp s hs R₀ hR₀ j u ell hu N) (by positivity)
    _ = _ := by rw [div_pow, div_eq_mul_inv]; ring

/-- The order for accuracy `Q = 2k` in `main:eq:smoothing-combined` is fixed
before every history. It uses the paper's coefficient exponent `34/35`. -/
def smoothingTailOrder (k : ℕ) : ℕ := 140 * k

/-- The chosen order gives exactly the exponent required by the geometric
mean in `main:eq:smoothing-combined`. -/
theorem smoothingTailOrder_decay (k : ℕ) :
    (1 - coefficientExponent) * (smoothingTailOrder k : ℝ) = 4 * k := by
  simp only [smoothingTailOrder, Nat.cast_mul, Nat.cast_ofNat, coefficientExponent]
  ring

/-- The high-tail scale at the chosen order is `R^(-4k)`; its geometric mean
with the small tail yields the `R^(-2k)` needed by `ComponentEstimates.smoothing`. -/
theorem smoothingTailOrder_scale {R : ℝ} (hR : 0 < R) (k : ℕ) :
    (R ^ coefficientExponent / R) ^ smoothingTailOrder k = R ^ (-4 * (k : ℝ)) := by
  have heq : R ^ coefficientExponent / R = R ^ (coefficientExponent - 1) := by
    rw [Real.rpow_sub hR, Real.rpow_one]
  rw [heq]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
  congr 1
  nlinarith [smoothingTailOrder_decay k]

end JanetCartan.DefectSmoothing
