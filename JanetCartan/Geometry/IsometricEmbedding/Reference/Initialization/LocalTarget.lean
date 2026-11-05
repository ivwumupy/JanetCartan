module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Dilation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Local target estimates for fixed reference initialization

The metric in `main:prop:seed` is only assumed smooth on a neighborhood.
A cutoff extension allows reuse of the checked global dilation estimate.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius Topology
open Set
namespace JanetCartan

variable {n : ℕ}

/-- `main:prop:seed`: extend a local smooth metric field near zero; no positivity
away from the agreement ball is asserted or needed. -/
theorem exists_smooth_metric_extension_near_zero {g : MetricField n} {U : Set (Euclidean n)}
    (hU : IsOpen U) (h0 : (0 : Euclidean n) ∈ U) (hg : ContDiffOn ℝ ∞ g U) :
    ∃ a : ℝ, 0 < a ∧ Metric.ball 0 a ⊆ U ∧
      ∃ f : MetricField n, ContDiff ℝ ∞ f ∧ EqOn f g (Metric.ball 0 a) := by
  obtain ⟨d, hd, hds⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  let b : ContDiffBump (0 : Euclidean n) :=
    ⟨d / 4, d / 2, by positivity, by linarith⟩
  have hbU : tsupport b ⊆ U := by
    rw [b.tsupport_eq]
    apply Subset.trans _ hds
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  refine ⟨d / 4, by positivity, (Metric.ball_subset_ball (by linarith)).trans hds,
    fun x ↦ b x • g x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact b.contDiff.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds hx))
    · have hxb : x ∉ tsupport b := fun h ↦ hx (hbU h)
      apply (contDiffAt_const (c := (0 : MetricTensor n))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxb] with y hy
      simp [hy]
  · intro x hx
    change b x • g x = g x
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx), one_smul]

/-- `main:eq:seed-small`: on a fixed chart and for a fixed positive reference
scale, a locally smooth normalized target has uniform `O(s)` bounds at every
finite derivative order. The interval and all domain choices precede the order. -/
theorem exists_local_target_dilation_bounds (D : LocalDomain) {ρ : ℝ} (hρ : 0 < ρ)
    {g : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (h0 : (0 : Euclidean n) ∈ U) (hg : ContDiffOn ℝ ∞ g U) (hg0 : g 0 = 1) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
      (∀ s ∈ Icc (0 : ℝ) s₀, ∀ x ∈ D.closureChart n, (s * ρ) • x ∈ U) ∧
      ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Icc (0 : ℝ) s₀,
        cNorm (D.closureChart n) r (fun x ↦ g ((s * ρ) • x) - 1) ≤ C * s := by
  obtain ⟨a, ha, haU, f, hf, hfg⟩ := exists_smooth_metric_extension_near_zero hU h0 hg
  let s₀ := min 1 (a / (2 * (ρ + 1)))
  have hs₀ : 0 < s₀ := lt_min zero_lt_one (by positivity)
  have hball (s : ℝ) (hs : s ∈ Icc (0 : ℝ) s₀) (x : Euclidean n)
      (hx : x ∈ D.closureChart n) : (s * ρ) • x ∈ Metric.ball 0 a := by
    have hxnorm : ‖x‖ ≤ 1 := by
      have hx' : ‖x‖ ≤ D.chartRadius := by simpa [LocalDomain.closureChart] using hx
      linarith [D.chartRadius_lt_half]
    have hs' : s * (2 * (ρ + 1)) ≤ a :=
      (le_div_iff₀ (by positivity)).mp (hs.2.trans (min_le_right _ _))
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hs.1 hρ.le)]
    have hnorm := mul_le_mul_of_nonneg_left hxnorm (mul_nonneg hs.1 hρ.le)
    nlinarith
  have hf0 : f 0 = 1 := (hfg (Metric.mem_ball_self ha)).trans hg0
  have hfρ : ContDiff ℝ ∞ (fun x ↦ f (ρ • x)) :=
    hf.comp (contDiff_id.const_smul ρ)
  refine ⟨s₀, hs₀, min_le_left _ _, fun s hs x hx ↦ haU (hball s hs x hx), ?_⟩
  intro r
  obtain ⟨C, hC, hbound⟩ := exists_cNorm_dilation_sub_const_bound
    (isCompact_closedBall (0 : Euclidean n) D.chartRadius) hfρ r
  refine ⟨C, hC, ?_⟩
  intro s hs
  have hnorm : cNorm (D.closureChart n) r (fun x ↦ g ((s * ρ) • x) - 1) =
      cNorm (D.closureChart n) r (fun x ↦ f (ρ • (s • x)) - f (ρ • 0)) := by
    unfold cNorm
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Set.image_congr
    intro x hx
    have heq : (fun y ↦ g ((s * ρ) • y) - 1) =ᶠ[𝓝 x]
        (fun y ↦ f (ρ • (s • y)) - f (ρ • 0)) := by
      have hopen : IsOpen {y : Euclidean n | (s * ρ) • y ∈ Metric.ball 0 a} :=
        Metric.isOpen_ball.preimage (continuous_id.const_smul (s * ρ))
      have hpre := hopen.mem_nhds (hball s hs x hx)
      filter_upwards [hpre] with y hy
      simp only [smul_zero, hf0, smul_smul, mul_comm ρ s, hfg hy]
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
  rw [hnorm]
  exact hbound s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩

end JanetCartan
