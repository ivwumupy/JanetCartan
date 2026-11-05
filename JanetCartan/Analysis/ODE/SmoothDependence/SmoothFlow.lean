module

public import JanetCartan.Analysis.ODE.SmoothDependence.DifferentiableFlow
public import JanetCartan.Analysis.ODE.SmoothDependence.FlowRegularity

/-!
# Smooth local flows in prescribed open sets

The local flow needed for `app:lem:common-hamilton-phase` is constructed by
Picard–Lindelöf and upgraded by variational induction. For a smooth field, one
bounded open flow domain works for every derivative order.
-/

@[expose] public section

open Set Metric
open scoped Topology NNReal

namespace JanetCartan.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `app:lem:common-hamilton-phase`: a `Cⁿ` autonomous vector field, with
`1 ≤ n ≤ ∞`, has a jointly `Cⁿ` local flow on a positive-radius ball times a
two-sided open time interval. Taking `n = ∞` gives a single smooth flow domain
for all derivative orders. On the closed product domain the flow is continuous,
uniformly Lipschitz in initial data, and stays in the prescribed open set.
Its actual initial-data derivative solves the variational IVP throughout the
open time interval. -/
theorem exists_contDiffOn_localFlow_in_open (n : ℕ∞) (hn : 1 ≤ n)
    {f : E → E} {x₀ : E} {U : Set E} (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hf : ContDiffOn ℝ n f U) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : E × ℝ → E,
      ContDiffOn ℝ n Φ (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
      ContinuousOn Φ (closedBall x₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)) ∧
      (∀ x ∈ closedBall x₀ r, Φ (x, t₀) = x) ∧
      (∀ x ∈ closedBall x₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt (fun s ↦ Φ (x, s)) (f (Φ (x, t))) t) ∧
      (∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), Φ (x, t) ∈ U) ∧
      (∀ x ∈ ball x₀ r, flowInitialDerivative Φ x t₀ = ContinuousLinearMap.id ℝ E) ∧
      (∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt (flowInitialDerivative Φ x)
          ((fderiv ℝ f (Φ (x, t))).comp (flowInitialDerivative Φ x t)) t) ∧
      ∃ K : ℝ≥0, ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
        LipschitzOnWith K (fun x ↦ Φ (x, t)) (closedBall x₀ r) := by
  have hf₁ : ContDiffOn ℝ 1 f U := hf.of_le (by exact_mod_cast hn)
  obtain ⟨r, hr, ε, hε, Φ, hcd, hc, hi, hd, hmem, hJ₀, hJ, K, hK⟩ :=
    exists_contDiffOn_one_localFlow_in_open hU hx₀ hf₁ t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hreg := contDiffOn_localFlow n hU hf isOpen_ball ht₀ hcd.continuousOn
    (fun x hx t ht ↦ hmem x (ball_subset_closedBall hx) t (Ioo_subset_Icc_self ht))
    (fun x hx ↦ hi x (ball_subset_closedBall hx))
    (fun x hx t ht ↦ hd x (ball_subset_closedBall hx) t ht)
    (fun t ht ↦ (hK t (Ioo_subset_Icc_self ht)).mono ball_subset_closedBall)
  exact ⟨r, hr, ε, hε, Φ, hreg, hc, hi, hd, hmem, hJ₀, hJ, K, hK⟩

end JanetCartan.ODE
