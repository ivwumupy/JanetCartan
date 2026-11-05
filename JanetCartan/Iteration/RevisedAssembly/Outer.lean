module

public import JanetCartan.Iteration.RevisedGlobal
public import JanetCartan.Iteration.RevisedConvergence
public import JanetCartan.Analysis.PhysicalBernstein

/-!
# The revised global outer construction from its actual finite-step input

This is the backward join for paper-v2 §18, `main:eq:initial-error`,
`main:eq:final-Cr`, and the Euclidean consumer of `main:thm:main`.
The finite-prefix recursion constructs the increments. The genuine physical
Bernstein theorem supplies all their derivative bounds on those same global
representatives. A single target dilation is chosen after the thresholds, and
one smooth sum is used at every order.

Only the analytic `RevisedGlobal.UniformHistoryCorrection` remains as a step
hypothesis. This file does not claim to construct its wave, mean, pair or cutoff
inputs, and therefore does not prove the unconditional main theorem.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RevisedGlobal.UniformHistoryCorrection

variable {n N : ℕ} {G : Euclidean n → Euclidean N} {D : Set (Euclidean n)}
  {g : ℝ → MetricField n} {s₀ B Tref : ℝ} {kMin : ℕ} {C T : ℕ → ℝ}

/-- §18: the actual physical finite-step contract and arbitrarily small initial
errors give one smooth isometric sum. Neither an infinite sequence nor any
increment derivative estimates are hypotheses: recursion and Bernstein produce
them. The interval and thresholds precede the single choice of `s`. -/
theorem exists_smooth_isometric_limit
    (h : UniformHistoryCorrection G D g s₀ kMin B Tref C T)
    (hG : ContDiff ℝ ∞ G)
    (hg : ∀ s, 0 < s → s ≤ s₀ → ContinuousOn (g s) D)
    (hgap : RevisedScales.cubicLoss n + 2 * growthExponent + 4 <
      (3 - 2 * growthExponent) * (kMin : ℝ))
    (hinitial : ∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ s₀ ∧
      cNorm D 0 (inducedMetric G - g s) ≤ η) :
    ∃ (s : ℝ) (u : ℕ → SchwartzMap (Euclidean n) (Euclidean N)),
      0 < s ∧ s ≤ s₀ ∧
      ContDiff ℝ ∞ (RevisedConvergence.limitMap G (fun j ↦ ⇑(u j))) ∧
      (∀ r : ℕ, TendstoUniformly
        (fun j ↦ iteratedFDeriv ℝ r (currentHistoryMap G (fun i ↦ ⇑(u i)) j))
        (iteratedFDeriv ℝ r (RevisedConvergence.limitMap G (fun i ↦ ⇑(u i)))) atTop) ∧
      IsIsometricOn (g s) (RevisedConvergence.limitMap G (fun j ↦ ⇑(u j))) D := by
  obtain ⟨H, _hH, hHbounds, hconstruct⟩ :=
    h.exists_adaptive_correction_sequence hgap (fun _ ↦ 2)
  let R₀ : ℝ := H kMin
  have hR₀two : 2 ≤ R₀ := (hHbounds kMin).1
  have hR₀ : 1 < R₀ := by linarith
  obtain ⟨s, hs, hs₀, hinit⟩ :=
    hinitial ((R₀ ^ (-(kMin : ℝ))) ^ 2) (by positivity)
  obtain ⟨_hk, _hthreshold, u, hu, _hprefix, hmetric⟩ :=
    hconstruct R₀ s le_rfl hs hs₀ hinit
  let Cderiv : ℕ → ℝ := fun r ↦ PhysicalBernstein.bernsteinConstant n r *
    B ^ ((r : ℝ) + (n : ℝ) / 2)
  have hB : 0 < B := zero_lt_one.trans_le h.one_le_band
  have hderiv : ∀ r, ∀ᶠ j in atTop, ∀ x,
      ‖iteratedFDeriv ℝ r (u j : Euclidean n → Euclidean N) x‖ ≤
        RevisedConvergence.derivativeBudget n H kMin R₀ Cderiv r j := by
    intro r
    apply Eventually.of_forall
    intro j x
    have hR : 0 < iterationScale R₀ growthExponent j :=
      Real.rpow_pos_of_pos (zero_lt_one.trans hR₀) _
    exact RevisedConvergence.derivative_bound_of_physical_bounds hR hB.le
      (PhysicalBernstein.bernsteinConstant_pos n r).le
      (PhysicalBernstein.norm_iteratedFDeriv_le (u j)
        (mul_pos hB (Real.rpow_pos_of_pos hR _)) (hu j).1 r x) (hu j).2
  obtain ⟨hlim, hconv, hiso⟩ := RevisedConvergence.smooth_isometric_limit_of_revised_bounds
    H kMin hR₀ h.isCompact hG (fun j ↦ (u j).smooth') (hg s hs hs₀) hderiv hmetric
  exact ⟨s, u, hs, hs₀, hlim, hconv, hiso⟩

/-- §18, `main:thm:main`: the precise Euclidean local-realization conclusion
needed by the coordinate-transfer theorem. This closes the recursion, actual
Bernstein, all-order convergence, and the same `sρ`/`A` restoration behind that
consumer. The original-data producer of the revised finite step is still an
explicit hypothesis; no successful infinite construction is assumed. -/
theorem exists_local_metric_of_initial_defects
    {g₀ : MetricField n} {W V : Set (Euclidean n)}
    (A : MetricTensor n) (hA : IsUnit A) {ρ : ℝ} (hρ : 0 < ρ)
    (h : UniformHistoryCorrection G D
      (fun s ↦ scaledMetric (coordinatePullback g₀ A) (s * ρ)) s₀ kMin B Tref C T)
    (hG : ContDiff ℝ ∞ G) (hW : IsOpen W) (hW0 : (0 : Euclidean n) ∈ W)
    (hWD : W ⊆ D) (hV : IsOpen V) (hV0 : (0 : Euclidean n) ∈ V)
    (htarget : ∀ s, 0 < s → s ≤ s₀ →
      ContinuousOn (scaledMetric (coordinatePullback g₀ A) (s * ρ)) D)
    (hgap : RevisedScales.cubicLoss n + 2 * growthExponent + 4 <
      (3 - 2 * growthExponent) * (kMin : ℝ))
    (hinitial : ∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ s₀ ∧
      cNorm D 0 (inducedMetric G - scaledMetric (coordinatePullback g₀ A) (s * ρ)) ≤ η) :
    ∃ U : Set (Euclidean n), IsOpen U ∧ (0 : Euclidean n) ∈ U ∧ U ⊆ V ∧
      ∃ F : Euclidean n → Euclidean N, ContDiffOn ℝ ∞ F U ∧ IsIsometricOn g₀ F U := by
  obtain ⟨s, u, hs, _hs₀, hlim, _hconv, hiso⟩ :=
    h.exists_smooth_isometric_limit hG htarget hgap hinitial
  obtain ⟨hU, hU0, hreg, hmetric⟩ := RevisedConvergence.restore_same_parameters
    A hA hs hρ hW hW0 hlim (fun _ hx ↦ hiso (hWD hx))
  exact ⟨RevisedConvergence.restoredDomain A s ρ W ∩ V, hU.inter hV, ⟨hU0, hV0⟩,
    Set.inter_subset_right,
    RevisedConvergence.restoredMap A s ρ (RevisedConvergence.limitMap G (fun j ↦ ⇑(u j))),
    hreg.mono Set.inter_subset_left, fun _ hx ↦ hmetric hx.1⟩

end JanetCartan.RevisedGlobal.UniformHistoryCorrection
