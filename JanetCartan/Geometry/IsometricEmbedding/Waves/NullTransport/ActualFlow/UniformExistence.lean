module

public import JanetCartan.Analysis.ODE.SmoothDependence.SmoothFlow
public import JanetCartan.Analysis.ODE.HigherVariational
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# A fixed existence interval from the low field bounds

The autonomous lift used in `app:ch_waves:thm:leading` needs a time interval
chosen from geometric buffers and low coefficients. This specializes the
Picard construction to a prescribed closed state ball and initial half-ball.
Smoothness is proved on that same domain, at every order.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff NNReal

namespace JanetCartan.NullTransport.ActualFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The null-characteristic existence time for a state buffer of radius `R`
and a low bound `M` (`app:ch_waves:thm:leading`). -/
def existenceTime (R M : ℝ) : ℝ := R / (4 * (M + 1))

/-- The prescribed existence time is positive (`app:ch_waves:thm:leading`). -/
theorem existenceTime_pos {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M) :
    0 < existenceTime R M := by unfold existenceTime; positivity

/-- A bounded smooth autonomous field has a smooth flow on the fixed initial
half-ball and the explicit two-sided interval. This is the Picard step for
`exists_lifted_characteristics`; no flow or variational identity is assumed.
The actual first variation is also constructed (`app:ch_waves:thm:leading`). -/
theorem exists_smoothFlow_on_fixed_ball
    {V : E → E} {Ω : Set E} {q₀ : E} {R M : ℝ}
    (hΩ : IsOpen Ω) (hV : ContDiffOn ℝ ∞ V Ω)
    (hR : 0 < R) (hM : 0 ≤ M) (hbuffer : closedBall q₀ R ⊆ Ω)
    (hvalue : ∀ q ∈ closedBall q₀ R, ‖V q‖ ≤ M)
    (hderiv : ∀ q ∈ closedBall q₀ R, ‖fderiv ℝ V q‖ ≤ M) :
    ∃ Ψ : E × ℝ → E,
      ContDiffOn ℝ ∞ Ψ
        (ball q₀ (R / 2) ×ˢ Ioo (-existenceTime R M) (existenceTime R M)) ∧
      ContinuousOn Ψ
        (closedBall q₀ (R / 2) ×ˢ Icc (-existenceTime R M) (existenceTime R M)) ∧
      (∀ q ∈ closedBall q₀ (R / 2), Ψ (q, 0) = q) ∧
      (∀ q ∈ closedBall q₀ (R / 2), ∀ t ∈ Ioo (-existenceTime R M) (existenceTime R M),
        HasDerivAt (fun s ↦ Ψ (q, s)) (V (Ψ (q, t))) t) ∧
      (∀ q ∈ closedBall q₀ (R / 2), ∀ t ∈ Icc (-existenceTime R M) (existenceTime R M),
        Ψ (q, t) ∈ closedBall q₀ R) ∧
      (∀ q ∈ ball q₀ (R / 2), ODE.flowInitialDerivative Ψ q 0 =
        ContinuousLinearMap.id ℝ E) ∧
      (∀ q ∈ ball q₀ (R / 2), ∀ t ∈ Ioo (-existenceTime R M) (existenceTime R M),
        HasDerivAt (ODE.flowInitialDerivative Ψ q)
          ((fderiv ℝ V (Ψ (q, t))).comp (ODE.flowInitialDerivative Ψ q t)) t) ∧
      (∀ a b : ℝ, -existenceTime R M < a → b < existenceTime R M →
        ∀ s ⊆ ball q₀ (R / 2), ∀ j : ℕ,
          HasJetEvolutionOn (fun t q ↦ Ψ (q, t)) s j a b
            (fun k t q ↦ ODE.jetEvolutionCoefficient k V (Ψ (q, t)))
            (fun k t q ↦ ODE.jetEvolutionForcing k V (fun p ↦ Ψ (p, t)) q)) := by
  let ε := existenceTime R M
  have hε : 0 < ε := existenceTime_pos hR hM
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hlip : LipschitzOnWith ⟨M, hM⟩ V (closedBall q₀ R) :=
    (convex_closedBall q₀ R).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun q hq ↦ (hV.contDiffAt (hΩ.mem_nhds (hbuffer hq))).differentiableAt (by simp))
      (fun q hq ↦ by exact_mod_cast hderiv q hq)
  have hpl : IsPicardLindelof (fun _ ↦ V) ⟨0, h0.1.le, h0.2.le⟩ q₀
      ⟨R, hR.le⟩ ⟨R / 2, (half_pos hR).le⟩ ⟨M, hM⟩ ⟨M, hM⟩ := by
    refine ⟨fun _ _ ↦ hlip, fun _ _ ↦ continuousOn_const, fun _ _ ↦ hvalue, ?_⟩
    change M * max (ε - 0) (0 - -ε) ≤ R - R / 2
    simp only [sub_zero, sub_neg_eq_add, zero_add, max_self]
    have hden : 0 < 4 * (M + 1) := by positivity
    dsimp [ε, existenceTime]
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  obtain ⟨Ψ, hi, hd, hr, hc, L, hL⟩ := ODE.exists_localFlow_with_range hpl
  have hode (q) (hq : q ∈ closedBall q₀ (R / 2)) (t) (ht : t ∈ Ioo (-ε) ε) :
      HasDerivAt (fun s ↦ Ψ (q, s)) (V (Ψ (q, t))) t :=
    (hd q hq t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hcont := hc.mono (prod_mono ball_subset_closedBall Ioo_subset_Icc_self)
  have hrange (q) (hq : q ∈ ball q₀ (R / 2)) (t) (ht : t ∈ Ioo (-ε) ε) :=
    hbuffer (hr q (ball_subset_closedBall hq) t (Ioo_subset_Icc_self ht))
  have hinit (q) (hq : q ∈ ball q₀ (R / 2)) := hi q (ball_subset_closedBall hq)
  have hode' (q) (hq : q ∈ ball q₀ (R / 2)) := hode q (ball_subset_closedBall hq)
  have hlip' (t) (ht : t ∈ Ioo (-ε) ε) :=
    (hL t (Ioo_subset_Icc_self ht)).mono ball_subset_closedBall
  obtain ⟨_, hJ₀, hJ⟩ := ODE.contDiffOn_flow_and_variational_equation hΩ
    (hV.of_le (by simp)) isOpen_ball h0 hcont hrange hinit hode' hlip'
  have hSmooth := ODE.contDiffOn_localFlow ⊤ hΩ hV isOpen_ball h0 hcont hrange
    hinit hode' hlip'
  refine ⟨Ψ, hSmooth, hc, hi, hode, hr, hJ₀, hJ, ?_⟩
  intro a b ha hb s hs j
  exact ODE.hasJetEvolutionOn_of_ode isOpen_ball hΩ ha hb hSmooth hV
    (fun q hq ↦ hrange q.1 hq.1 q.2 hq.2) hode' hs j

end JanetCartan.NullTransport.ActualFlow
