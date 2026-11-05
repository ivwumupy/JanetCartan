module
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingScaled
public import JanetCartan.Iteration.RevisedStage.Accuracy
public import JanetCartan.Iteration.RevisedUniform.Scales

/-!
# One physical preparation at the prescribed stage accuracy

The fixed initial threshold is not the current-frequency requirement. Select
the moment order of the joint five-order scheme, and use BOTH real tails of
the original tensor on its same positive interval. A current-frequency maximum
pays for that approximation and for the measured target at all orders.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalMean.OriginalCompleteForcing

/-- The finite-moment order from the manuscript's *joint* step-accuracy
selection, with a positive reserve. It is fixed before scale and history and
is not the protected reference order (`new:eq:step-accuracies`). -/
def stepMomentOrder (n k reserve : ℕ) : ℕ :=
  (RevisedUniform.exists_stage_orders (n := n) (k := k) (reserve := max 1 reserve)).choose

theorem stepMomentOrder_spec (n k reserve : ℕ) :
    1 ≤ stepMomentOrder n k reserve ∧
      4 * (k : ℝ) < (1 - coefficientExponent) * (stepMomentOrder n k reserve : ℕ) := by
  obtain ⟨_,_,_,_,hm,_,_,_,_,haccuracy,_,_,_,_⟩ :=
    (RevisedUniform.exists_stage_orders (n := n) (k := k) (reserve := max 1 reserve)).choose_spec
  exact ⟨(Nat.le_max_left 1 reserve).trans hm,haccuracy⟩

/-- On the same positive interval as the actual measured source, a single
prehistory threshold gives both its original measurement reach and the
physical `δ R^(-2k)` smoothing tail. Both primitive tails of the *same*
finite-moment tensor come from the original target-history smoother; neither
is assumed. This is the smoothing term of `main:eq:metric-two-errors`. -/
theorem exists_prescribed_smoothing_reach {n : ℕ} (D : LocalDomain) (G : FlatReference n)
    {ρ : ℝ} (hρ : 0 < ρ) {g : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (h0 : (0 : Euclidean n) ∈ U) (hg : IsRiemannianMetricOn g U) (hg0 : g 0 = 1)
    {B : ℝ} (hB : 1 ≤ B) {kMin : ℕ}
    (hi : RevisedScales.displacementLoss n + bandExponent * (1 + (n : ℝ) / 2) + 2 < (kMin : ℝ))
    (CM : ℕ → ℝ) (k reserve : ℕ) :
    let s₀ := (PhysicalSmoothing.exists_original_target_history_smoothing D G hρ hU h0 hg hg0 hB hi).choose
    let m := stepMomentOrder n k reserve
    ∃ S C : ℝ, 2 ≤ S ∧ 0 ≤ C ∧ uniformTargetFrequency n D CM m (stepMomentOrder_spec n k reserve).1 ≤ S ∧
      ∀ s ∈ Icc (0 : ℝ) s₀, ∀ R₀ : ℝ, 2 ≤ R₀ →
        ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n))) (ell : Fin j → ℕ),
        RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
        let R := iterationScale R₀ growthExponent j
        let δ := R ^ (-(k : ℝ))
        let gs := scaledMetric g (s * ρ)
        S ≤ R → cNorm (D.core n) 0 (inducedMetric (RevisedGlobal.finiteMap G.map u) - gs) ≤ δ^2 →
        ∀ x ∈ D.core n,
          ‖PhysicalSmoothing.smoothedDefect D R m gs G.map u x - PhysicalSmoothing.historyDefect gs G.map u x‖ ≤
            C * δ * R ^ (-(2 * (k : ℝ))) := by
  intro s₀ m
  have hdata := (PhysicalSmoothing.exists_original_target_history_smoothing D G hρ hU h0 hg hg0 hB hi).choose_spec
  obtain ⟨_,_,_,K,_,_,hmom⟩ := hdata
  have hm : 1 ≤ m := (stepMomentOrder_spec n k reserve).1
  obtain ⟨Rmin,L,Ln,Cs,Ch,h2,_,_,_,hCs,hCh,all⟩ := hmom m hm
  let C := max Cs Ch
  let F := uniformTargetFrequency n D CM m hm
  let S := max Rmin F
  have hC : 0 ≤ C := hCs.trans (le_max_left _ _)
  refine ⟨S,C,h2.trans (le_max_left _ _),hC,le_max_right _ _,?_⟩
  intro s hs R₀ hR₀ j u ell hu R δ gs hS hsmall x hx
  have hmin : Rmin ≤ R := (le_max_left _ _).trans hS
  have hR : 1 ≤ R := (by norm_num : (1:ℝ) ≤ 2).trans (h2.trans hmin)
  have hδ : 0 < δ := prescribed_defect_pos hR₀ j k
  obtain ⟨_,_,_,_,_,_,hlow,hhigh,_⟩ := all s hs R₀ hR₀ j u ell hu hmin δ hδ hsmall
  have hmQ : 2 * (2 * (k : ℝ)) < (1 - coefficientExponent) * (m : ℝ) := by
    rw [show 2 * (2 * (k : ℝ)) = 4 * (k : ℝ) by ring]; exact (stepMomentOrder_spec n k reserve).2
  have hratio : 0 ≤ (R ^ coefficientExponent / R)^m :=
    pow_nonneg (div_nonneg (Real.rpow_nonneg (zero_le_one.trans hR) _) (zero_le_one.trans hR)) _
  exact RevisedStage.smoothing_error_le_of_accuracy (norm_nonneg _) hC hδ.le hR hmQ
    ((hlow x hx).trans (mul_le_mul_of_nonneg_right (le_max_left Cs Ch) (sq_nonneg _)))
    ((hhigh x hx).trans (mul_le_mul_of_nonneg_right (le_max_right Cs Ch) hratio))
end JanetCartan.PhysicalMean.OriginalCompleteForcing
end
