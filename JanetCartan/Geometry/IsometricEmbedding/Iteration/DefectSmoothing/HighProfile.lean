module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.History
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.HighProfile.Metric
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.LocalTarget

/-!
# High derivative bounds for the actual finite-history defect

The profile needed in `main:lem:smoothing` and `main:eq:smoothing-high` is
constructed from the finite-prefix budgets and the locally smooth normalized
target. One dilation interval and all constants precede the dilation, initial
scale, stage, and history. No small-defect or extension estimate is used.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
open Set

set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.DefectSmoothing

private theorem cNorm_constant_tensor_le {n : ℕ} (K : Set (Euclidean n))
    (r : ℕ) (v : MetricTensor n) : cNorm K r (fun _ ↦ v) ≤ ‖v‖ := by
  induction r with
  | zero =>
    rw [cNorm_order_zero]
    exact Real.sSup_le (by rintro _ ⟨x, _, rfl⟩; exact le_rfl) (norm_nonneg _)
  | succ r ih =>
    rw [cNorm_succ]
    have hz : sSup ((fun x : Euclidean n ↦
        ‖iteratedFDeriv ℝ (r + 1) (fun _ : Euclidean n ↦ v) x‖) '' K) ≤ 0 := by
      apply Real.sSup_le _ le_rfl
      rintro _ ⟨x, _, rfl⟩
      simp [iteratedFDeriv_succ_const]
    linarith

/-- `main:lem:smoothing`, the actual defect profile used in
`main:eq:smoothing-high`. The target bounds are supplied by local dilation,
and the map bounds by the admissible finite history at baseline one. The
constants and the single positive dilation interval precede every scale and
history. The extra range conclusion records where local target smoothness applies. -/
theorem exists_historyDefect_derivative_profile {n : ℕ}
    (D : LocalDomain) (G : FlatReference n) {ρ : ℝ} (hρ : 0 < ρ)
    {g : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (h0 : (0 : Euclidean n) ∈ U) (hg : ContDiffOn ℝ ∞ g U) (hg0 : g 0 = 1)
    {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (1 + (n : ℝ) / 2) + 2 < kMin) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
      (∀ s ∈ Icc (0 : ℝ) s₀, ∀ x ∈ D.closureChart n, (s * ρ) • x ∈ U) ∧
      ∃ C : ℕ → ℝ, (∀ r, 0 ≤ C r) ∧
        ∀ s ∈ Icc (0 : ℝ) s₀, ∀ R₀ : ℝ, 2 ≤ R₀ →
          ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
            (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
            ∀ r, cNorm (D.core n) r
              (historyDefect (fun x ↦ g ((s * ρ) • x)) G.map u) ≤
                C r * (iterationScale R₀ growthExponent j ^ coefficientExponent) ^ r := by
  obtain ⟨s₀, hs₀, hs₀1, hmaps, htarget⟩ :=
    exists_local_target_dilation_bounds D hρ hU h0 hg hg0
  choose A hA hAbound using htarget
  obtain ⟨P, hP, hprefix⟩ := FiniteHistoryBounds.exists_prefix_derivative_profile
    (K := D.core n) (G := G.map) (isCompact_closedBall _ _)
    (fun _ _ ↦ G.contDiff.contDiffAt) 1 (by simpa using horder)
  obtain ⟨B, hB, hmetric⟩ := exists_inducedMetric_derivative_profile
    (N := embeddingDimension n) P hP
  refine ⟨s₀, hs₀, hs₀1, hmaps,
    fun r ↦ A r + ‖(1 : MetricTensor n)‖ + B r,
    fun r ↦ add_nonneg (add_nonneg (hA r).le (norm_nonneg _)) (hB r), ?_⟩
  intro s hs R₀ hR₀ j u ell hu r
  let T := iterationScale R₀ growthExponent j ^ coefficientExponent
  have hT : 1 ≤ T := Real.one_le_rpow
    (Real.one_le_rpow (by linarith) (pow_nonneg (by norm_num [growthExponent]) _))
    (by norm_num [coefficientExponent])
  have hF := hu.contDiff_finiteHistoryMap G.contDiff
  have hp : HasDerivativeProfile (D.core n) (finiteHistoryMap G.map u) 1 T P :=
    hprefix R₀ hR₀ j u (fun i ↦ (ell i : ℝ))
      (fun i ↦ (hu i).2.1) (fun i ↦ (hu i).2.2.1) (fun i ↦ (hu i).2.2.2)
      (fun i ↦ Nat.cast_le.mpr (hu i).1) (D.core n) Subset.rfl
  have hm := hmetric (D.core n) (isCompact_closedBall _ _) T hT
    (finiteHistoryMap G.map u) hF hp r
  have hsub : D.core n ⊆ D.closureChart n :=
    Metric.closedBall_subset_closedBall D.coreRadius_lt_chartRadius.le
  have ht (x : Euclidean n) (hx : x ∈ D.closureChart n) :
      ContDiffAt ℝ r (fun y ↦ g ((s * ρ) • y)) x :=
    ((hg.contDiffAt (hU.mem_nhds (hmaps s hs x hx))).comp x
      (contDiff_id.const_smul (s * ρ)).contDiffAt).of_le (by simp)
  have htargetcore : cNorm (D.core n) r (fun x ↦ g ((s * ρ) • x)) ≤
      A r + ‖(1 : MetricTensor n)‖ := by
    have htriangle := cNorm_add_le_of_contDiffAt (s := D.core n)
      (f := fun x ↦ g ((s * ρ) • x) - 1) (g := fun _ ↦ (1 : MetricTensor n))
      (r := r) (isCompact_closedBall _ _)
      (fun x hx ↦ (ht x (hsub hx)).sub contDiffAt_const)
      (fun _ _ ↦ contDiffAt_const)
    have heq : (fun x ↦ g ((s * ρ) • x) - 1) + (fun _ ↦ (1 : MetricTensor n)) =
        (fun x ↦ g ((s * ρ) • x)) := by funext x; simp
    rw [heq] at htriangle
    apply htriangle.trans
    apply add_le_add _ (cNorm_constant_tensor_le _ _ _)
    calc
      _ ≤ cNorm (D.closureChart n) r (fun x ↦ g ((s * ρ) • x) - 1) :=
        cNorm_mono_set_of_contDiffAt hsub (isCompact_closedBall _ _)
          (fun x hx ↦ (ht x hx).sub contDiffAt_const)
      _ ≤ A r * s := hAbound r s hs
      _ ≤ A r := by simpa using mul_le_mul_of_nonneg_left (hs.2.trans hs₀1) (hA r).le
  have hmSmooth : ContDiff ℝ ∞ (inducedMetric (finiteHistoryMap G.map u)) :=
    contDiff_inducedMetric hF (by simp)
  have htriangle := cNorm_add_le_of_contDiffAt (s := D.core n)
    (f := fun x ↦ g ((s * ρ) • x)) (g := -inducedMetric (finiteHistoryMap G.map u))
    (r := r) (isCompact_closedBall _ _)
    (fun x hx ↦ ht x (hsub hx))
    (fun _ _ ↦ (hmSmooth.of_le (show (r : ℕ∞ω) ≤ ∞ by simp)).contDiffAt.neg)
  rw [cNorm_neg] at htriangle
  change cNorm (D.core n) r
    ((fun x ↦ g ((s * ρ) • x)) - inducedMetric (finiteHistoryMap G.map u)) ≤ _
  calc
    _ ≤ cNorm (D.core n) r (fun x ↦ g ((s * ρ) • x)) +
        cNorm (D.core n) r (inducedMetric (finiteHistoryMap G.map u)) := by
      simpa only [sub_eq_add_neg] using htriangle
    _ ≤ (A r + ‖(1 : MetricTensor n)‖) + B r * T ^ r := add_le_add htargetcore hm
    _ ≤ (A r + ‖(1 : MetricTensor n)‖) * T ^ r + B r * T ^ r := by
      exact add_le_add (le_mul_of_one_le_right
        (add_nonneg (hA r).le (norm_nonneg (1 : MetricTensor n))) (one_le_pow₀ hT)) le_rfl
    _ = _ := by dsimp [T]; ring

end JanetCartan.DefectSmoothing
