module

public import JanetCartan.Iteration.PhysicalSmoothing.Basic
public import JanetCartan.Iteration.PhysicalHistory

/-!
# The actual physical defect has the current coefficient-scale profile

For `main:eq:smoothing-high` in `paper-v2.tex`, the same original normalized
local target and prescribed reference produce one target interval and one
all-order defect profile before every physical prefix, stage and accuracy.
The map profile is derived from genuine physical Fourier/L² history budgets;
the existing metric Leibniz theorem is then applied to the actual current map.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalSmoothing

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

/-- `main:lem:smoothing`: construct the high-order profile of the SAME signed
physical defect from the original local metric and actual admissible prefixes.
The target interval and all constants precede all histories and smoothing orders.
The prescribed source scale and reference are never changed. -/
theorem exists_historyDefect_derivative_profile {n : ℕ}
    (D : LocalDomain) (G : FlatReference n) {ρ : ℝ} (hρ : 0 < ρ)
    {g : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (h0 : (0 : Euclidean n) ∈ U) (hg : ContDiffOn ℝ ∞ g U) (hg0 : g 0 = 1)
    {B : ℝ} (hB : 1 ≤ B) {kMin : ℕ}
    (horder : RevisedScales.displacementLoss n + bandExponent * (1 + (n : ℝ) / 2) + 2 < kMin) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
      (∀ s ∈ Icc (0 : ℝ) s₀, ∀ x ∈ D.closureChart n, (s * ρ) • x ∈ U) ∧
      ∃ C : ℕ → ℝ, (∀ r, 0 ≤ C r) ∧
        ∀ s ∈ Icc (0 : ℝ) s₀, ∀ R₀ : ℝ, 2 ≤ R₀ →
          ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
            (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
            ∀ r, cNorm (D.core n) r
              (historyDefect (scaledMetric g (s * ρ)) G.map u) ≤
                C r * (iterationScale R₀ growthExponent j ^ coefficientExponent) ^ r := by
  obtain ⟨s₀, hs₀, hs₀1, hmaps, htarget⟩ :=
    exists_local_target_dilation_bounds D hρ hU h0 hg hg0
  choose A hA hAbound using htarget
  obtain ⟨P, hP, hprefix⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (K := D.core n) (G := G.map) (rStar := 1) (isCompact_closedBall _ _)
    (fun _ _ ↦ G.contDiff.contDiffAt) hB (by simpa using horder)
  obtain ⟨C, hC, hmetric⟩ := DefectSmoothing.exists_inducedMetric_derivative_profile
    (N := embeddingDimension n) P hP
  refine ⟨s₀, hs₀, hs₀1, hmaps,
    fun r ↦ A r + ‖(1 : MetricTensor n)‖ + C r,
    fun r ↦ add_nonneg (add_nonneg (hA r).le (norm_nonneg _)) (hC r), ?_⟩
  intro s hs R₀ hR₀ j u ell hu r
  let T := iterationScale R₀ growthExponent j ^ coefficientExponent
  have hT : 1 ≤ T := one_le_currentCoefficientScale (by linarith) j
  have hF : ContDiff ℝ ∞ (RevisedGlobal.finiteMap G.map u) :=
    G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  have hp : HasDerivativeProfile (D.core n) (RevisedGlobal.finiteMap G.map u) 1 T P :=
    hprefix R₀ hR₀ j u ell hu (D.core n) Subset.rfl
  have hm := hmetric (D.core n) (isCompact_closedBall _ _) T hT
    (RevisedGlobal.finiteMap G.map u) hF hp r
  have hsub : D.core n ⊆ D.closureChart n :=
    Metric.closedBall_subset_closedBall D.coreRadius_lt_chartRadius.le
  have ht (x : Euclidean n) (hx : x ∈ D.closureChart n) :
      ContDiffAt ℝ r (scaledMetric g (s * ρ)) x :=
    ((hg.contDiffAt (hU.mem_nhds (hmaps s hs x hx))).comp x
      (contDiff_id.const_smul (s * ρ)).contDiffAt).of_le (by simp)
  have htargetcore : cNorm (D.core n) r (scaledMetric g (s * ρ)) ≤
      A r + ‖(1 : MetricTensor n)‖ := by
    have htriangle := cNorm_add_le_of_contDiffAt (s := D.core n)
      (f := fun x ↦ g ((s * ρ) • x) - 1) (g := fun _ ↦ (1 : MetricTensor n))
      (r := r) (isCompact_closedBall _ _)
      (fun x hx ↦ (ht x (hsub hx)).sub contDiffAt_const)
      (fun _ _ ↦ contDiffAt_const)
    have heq : (fun x ↦ g ((s * ρ) • x) - 1) + (fun _ ↦ (1 : MetricTensor n)) =
        scaledMetric g (s * ρ) := by funext x; simp [scaledMetric]
    rw [heq] at htriangle
    apply htriangle.trans
    apply add_le_add _ (cNorm_constant_tensor_le _ _ _)
    calc
      _ ≤ cNorm (D.closureChart n) r (fun x ↦ g ((s * ρ) • x) - 1) :=
        cNorm_mono_set_of_contDiffAt hsub (isCompact_closedBall _ _)
          (fun x hx ↦ (ht x hx).sub contDiffAt_const)
      _ ≤ A r * s := hAbound r s hs
      _ ≤ A r := by simpa using mul_le_mul_of_nonneg_left (hs.2.trans hs₀1) (hA r).le
  have hmSmooth : ContDiff ℝ ∞ (inducedMetric (RevisedGlobal.finiteMap G.map u)) :=
    contDiff_inducedMetric hF (by simp)
  have htriangle := cNorm_add_le_of_contDiffAt (s := D.core n)
    (f := scaledMetric g (s * ρ)) (g := -inducedMetric (RevisedGlobal.finiteMap G.map u))
    (r := r) (isCompact_closedBall _ _)
    (fun x hx ↦ ht x (hsub hx))
    (fun _ _ ↦ (hmSmooth.of_le (show (r : ℕ∞ω) ≤ ∞ by simp)).contDiffAt.neg)
  rw [cNorm_neg] at htriangle
  change cNorm (D.core n) r
    (scaledMetric g (s * ρ) - inducedMetric (RevisedGlobal.finiteMap G.map u)) ≤ _
  calc
    _ ≤ cNorm (D.core n) r (scaledMetric g (s * ρ)) +
        cNorm (D.core n) r (inducedMetric (RevisedGlobal.finiteMap G.map u)) := by
      simpa only [sub_eq_add_neg] using htriangle
    _ ≤ (A r + ‖(1 : MetricTensor n)‖) + C r * T ^ r := add_le_add htargetcore hm
    _ ≤ (A r + ‖(1 : MetricTensor n)‖) * T ^ r + C r * T ^ r := by
      exact add_le_add (le_mul_of_one_le_right
        (add_nonneg (hA r).le (norm_nonneg (1 : MetricTensor n))) (one_le_pow₀ hT)) le_rfl
    _ = _ := by dsimp [T]; ring

end JanetCartan.PhysicalSmoothing
