module

public import JanetCartan.Analysis.ODE.SmoothDependence.LocalExistence
public import JanetCartan.Analysis.ODE.SmoothDependence.FirstDerivative

/-!
# Differentiable local flows in prescribed open sets

For `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`, combine Picard–Lindelöf with the identification
of the initial-data derivative. The flow is jointly `C¹` on a bounded open
product domain, while its range and continuity extend to the closed domain.
-/

@[expose] public section

open Set Metric
open scoped NNReal Topology

namespace JanetCartan.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `app:lem:common-hamilton-phase`: a `C¹` vector field on an open neighborhood
admits a jointly `C¹` local flow on a positive-radius ball times a two-sided
open time interval. The actual initial-data derivative satisfies the variational
IVP throughout this interval. The same flow stays in the prescribed neighborhood
even on the closed product domain, where it is continuous and uniformly
Lipschitz in the initial data. -/
theorem exists_contDiffOn_one_localFlow_in_open
    {f : E → E} {x₀ : E} {U : Set E} (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hf : ContDiffOn ℝ 1 f U) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : E × ℝ → E,
      ContDiffOn ℝ 1 Φ (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
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
  obtain ⟨r, hr, ε, hε, Φ, hc, hi, hd, hmem, K, hK⟩ :=
    exists_localFlow_in_open hU hx₀ (hf.contDiffAt (hU.mem_nhds hx₀)) t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  obtain ⟨hcd, hJ₀, hJ⟩ := contDiffOn_flow_and_variational_equation hU hf isOpen_ball ht₀
    (hc.mono (prod_mono ball_subset_closedBall Ioo_subset_Icc_self))
    (fun x hx t ht ↦ hmem x (ball_subset_closedBall hx) t (Ioo_subset_Icc_self ht))
    (fun x hx ↦ hi x (ball_subset_closedBall hx))
    (fun x hx t ht ↦ hd x (ball_subset_closedBall hx) t ht)
    (fun t ht ↦ (hK t (Ioo_subset_Icc_self ht)).mono ball_subset_closedBall)
  exact ⟨r, hr, ε, hε, Φ, hcd, hc, hi, hd, hmem, hJ₀, hJ, K, hK⟩

end JanetCartan.ODE
