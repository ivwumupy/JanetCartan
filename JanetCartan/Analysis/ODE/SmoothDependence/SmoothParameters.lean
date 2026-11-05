module

public import JanetCartan.Analysis.ODE.SmoothDependence.DifferentiableParameters
public import JanetCartan.Analysis.ODE.SmoothDependence.FlowRegularity

/-!
# Smooth parameterized local flows

For `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`, lift constant parameters to extra state
variables. The autonomous higher-regularity theorem then gives joint regularity
in parameters, initial states, and time. The local existence theorem includes
the actual parameter variational equation and the closed-domain range buffer.
-/

@[expose] public section

open Set Metric
open scoped Topology NNReal

namespace JanetCartan.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

/-- `app:lem:common-hamilton-phase`: a uniformly Lipschitz continuous family
of solutions inherits the joint finite or infinite regularity of its
parameterized vector field. Adjoining the constant parameter as a zero-velocity
state reduces this to autonomous flow regularity, without shrinking the domain. -/
theorem contDiffOn_parameterizedLocalFlow (n : ℕ∞)
    {V : P × E → E} {U s : Set (P × E)} {Φ : (P × E) × ℝ → E}
    {a b t₀ : ℝ} {K : ℝ≥0}
    (hU : IsOpen U) (hV : ContDiffOn ℝ n V U) (hs : IsOpen s)
    (ht₀ : t₀ ∈ Ioo a b) (hΦ : ContinuousOn Φ (s ×ˢ Ioo a b))
    (hrange : ∀ z ∈ s, ∀ t ∈ Ioo a b, (z.1, Φ (z, t)) ∈ U)
    (hinit : ∀ z ∈ s, Φ (z, t₀) = z.2)
    (hode : ∀ z ∈ s, ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ ↦ Φ (z, τ)) (V (z.1, Φ (z, t))) t)
    (hlip : ∀ t ∈ Ioo a b, LipschitzOnWith K (fun z ↦ Φ (z, t)) s) :
    ContDiffOn ℝ n Φ (s ×ˢ Ioo a b) := by
  let F : P × E → P × E := fun z ↦ (0, V z)
  let Ψ : (P × E) × ℝ → P × E := fun w ↦ (w.1.1, Φ w)
  have hF : ContDiffOn ℝ n F U := contDiffOn_const.prodMk hV
  have hΨ : ContinuousOn Ψ (s ×ˢ Ioo a b) :=
    continuous_fst.fst.continuousOn.prodMk hΦ
  have hi : ∀ z ∈ s, Ψ (z, t₀) = z := fun z hz ↦ Prod.ext rfl (hinit z hz)
  have hd : ∀ z ∈ s, ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ ↦ Ψ (z, τ)) (F (Ψ (z, t))) t :=
    fun z hz t ht ↦ (hasDerivAt_const t z.1).prodMk (hode z hz t ht)
  have hl : ∀ t ∈ Ioo a b,
      LipschitzOnWith (max 1 K) (fun z ↦ Ψ (z, t)) s :=
    fun t ht ↦ LipschitzWith.prod_fst.lipschitzOnWith.prodMk (hlip t ht)
  exact (contDiffOn_localFlow n hU hF hs ht₀ hΨ hrange hi hd hl).snd

/-- `app:lem:common-hamilton-phase`: a `Cⁿ` parameterized vector field, with
`1 ≤ n ≤ ∞`, admits a local flow jointly `Cⁿ` in the parameter, initial state,
and time on a bounded open product domain. At `n = ∞` the domain is common to
all orders. The closed domain retains continuity, a uniform Lipschitz bound,
and the prescribed range buffer. The actual parameter-and-state derivative
starts at the state projection and satisfies the full forced variational
equation on the entire open time interval. -/
theorem exists_contDiffOn_parameterized_localFlow_in_open (n : ℕ∞) (hn : 1 ≤ n)
    {V : P × E → E} {z₀ : P × E} {U : Set (P × E)}
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hV : ContDiffOn ℝ n V U) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : (P × E) × ℝ → E,
      ContDiffOn ℝ n Φ (ball z₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
      ContinuousOn Φ (closedBall z₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)) ∧
      (∀ z ∈ closedBall z₀ r, Φ (z, t₀) = z.2) ∧
      (∀ z ∈ closedBall z₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt (fun s ↦ Φ (z, s)) (V (z.1, Φ (z, t))) t) ∧
      (∀ z ∈ closedBall z₀ r, ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
        (z.1, Φ (z, t)) ∈ U) ∧
      (∀ z ∈ ball z₀ r,
        parameterizedFlowDerivative Φ z t₀ = ContinuousLinearMap.snd ℝ P E) ∧
      (∀ z ∈ ball z₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt (parameterizedFlowDerivative Φ z)
          ((fderiv ℝ V (z.1, Φ (z, t))).comp
            ((ContinuousLinearMap.fst ℝ P E).prod (parameterizedFlowDerivative Φ z t))) t) ∧
      ∃ K : ℝ≥0, ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
        LipschitzOnWith K (fun z ↦ Φ (z, t)) (closedBall z₀ r) := by
  have hV₁ : ContDiffOn ℝ 1 V U := hV.of_le (by exact_mod_cast hn)
  obtain ⟨r, hr, ε, hε, Φ, hcd, hc, hi, hd, hmem, hJ₀, hJ, K, hK⟩ :=
    exists_contDiffOn_one_parameterized_localFlow_in_open hU hz₀ hV₁ t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hreg := contDiffOn_parameterizedLocalFlow n hU hV isOpen_ball ht₀ hcd.continuousOn
    (fun z hz t ht ↦ hmem z (ball_subset_closedBall hz) t (Ioo_subset_Icc_self ht))
    (fun z hz ↦ hi z (ball_subset_closedBall hz))
    (fun z hz t ht ↦ hd z (ball_subset_closedBall hz) t ht)
    (fun t ht ↦ (hK t (Ioo_subset_Icc_self ht)).mono ball_subset_closedBall)
  exact ⟨r, hr, ε, hε, Φ, hreg, hc, hi, hd, hmem, hJ₀, hJ, K, hK⟩

end JanetCartan.ODE
