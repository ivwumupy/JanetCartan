module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.FlowStability.Spatial
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.FlowStability.TimeRescaling

/-!
# Joint finite-order continuity of actual flows

The space-time estimate in `app:lem:common-hamilton-phase` follows from the
spatial variational induction applied to an autonomous time augmentation.
Every augmented ODE, range, smoothness, and initial-section premise is proved
from `IsSmoothFlowOn`. Recovery costs a fixed factor at order `m` and no extra
field derivative. The consuming construction is finite-order continuity of
Hamilton phases after composition with their initial sections.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Topology
namespace JanetCartan.ODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem rescaling_buffers {r T ρ τ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hτ : 0 < τ) (hτT : τ < T) :
    ∃ l Rp q : ℝ, 0 < l ∧ ρ < Rp ∧ Rp < r ∧ 1 < q ∧
      l * ρ = τ ∧ l * q * Rp < T := by
  let l := τ / ρ
  have hl : 0 < l := div_pos hτ hρ
  have hlρ : l * ρ = τ := div_mul_cancel₀ _ hρ.ne'
  have hρT : ρ < T / l := (lt_div_iff₀ hl).mpr (by nlinarith)
  obtain ⟨Rp, hρRp, hRp⟩ := exists_between (lt_min hρr hρT)
  have hRp0 : 0 < Rp := hρ.trans hρRp
  have hlRp : l * Rp < T := by
    have := (lt_div_iff₀ hl).mp (lt_of_lt_of_le hRp (min_le_right _ _))
    nlinarith
  have hq : 1 < T / (l * Rp) := (lt_div_iff₀ (mul_pos hl hRp0)).mpr (by simpa)
  obtain ⟨q, hq1, hqT⟩ := exists_between hq
  refine ⟨l, Rp, q, hl, hρRp, hRp.trans_le (min_le_left _ _), hq1, hlρ, ?_⟩
  have := (lt_div_iff₀ (mul_pos hl hRp0)).mp hqT
  nlinarith

private theorem exists_cNorm_flow_sub_lt_of_radius_pos
    {W : Set E} {x₀ : E} {R r T ρ τ : ℝ} {V₀ : E → E} {Ψ₀ : E × ℝ → E}
    (hW : IsOpen W) (hR : 0 < R) (hRW : closedBall x₀ R ⊆ W)
    (hV₀ : ContDiffOn ℝ ∞ V₀ W) (hΨ₀ : IsSmoothFlowOn V₀ x₀ R r T Ψ₀)
    (hρ : 0 < ρ) (hρr : ρ < r) (hτ : 0 < τ) (hτT : τ < T)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (V : E → E) (Ψ : E × ℝ → E),
      ContDiffOn ℝ ∞ V W → IsSmoothFlowOn V x₀ R r T Ψ →
      cNorm (closedBall x₀ R) m (V - V₀) < δ →
      cNorm (closedBall x₀ ρ ×ˢ Icc (-τ) τ) m (Ψ - Ψ₀) < ε := by
  obtain ⟨l, Rp, q, hl, hρRp, hRpr, hq, hlρ, hlqRp⟩ :=
    rescaling_buffers hρ hρr hτ hτT
  let c := R / ρ
  have hc : 0 < c := div_pos hR hρ
  have hcρ : c * ρ ≤ R := (div_mul_cancel₀ R hρ.ne').le
  have hq0 : 0 < q := zero_lt_one.trans hq
  have htime : Ioo (0 - l * q * Rp) (0 + l * q * Rp) ⊆ Ioo (-T) T := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hsmooth {V : E → E} {Ψ : E × ℝ → E} (hΨ : IsSmoothFlowOn V x₀ R r T Ψ) :
      ContDiffOn ℝ ∞ Ψ (ball x₀ Rp ×ˢ Ioo (0 - l * q * Rp) (0 + l * q * Rp)) :=
    hΨ.smooth.mono (prod_mono (ball_subset_ball hRpr.le) htime)
  have hode {V : E → E} {Ψ : E × ℝ → E} (hΨ : IsSmoothFlowOn V x₀ R r T Ψ) :
      ∀ p ∈ ball (x₀, (0 : ℝ)) Rp, ∀ u ∈ Ioo (-q) q,
      HasDerivAt (fun v ↦ TimeRescaling.flow 0 l c Ψ (p, v))
        (TimeRescaling.field l c V (TimeRescaling.flow 0 l c Ψ (p, u))) u := by
    apply TimeRescaling.hasDerivAt_flow hl hq0 hc.ne'
    intro p hp t ht
    exact hΨ.hasDerivAt (ball_subset_closedBall (ball_subset_ball hRpr.le hp)) (htime ht)
  have hrange {V : E → E} {Ψ : E × ℝ → E} (hΨ : IsSmoothFlowOn V x₀ R r T Ψ) :
      ∀ p ∈ closedBall (x₀, (0 : ℝ)) ρ, ∀ u ∈ Ioo (-q) q,
        TimeRescaling.flow 0 l c Ψ (p, u) ∈ closedBall (x₀, 0) R := by
    apply TimeRescaling.flow_mem_closedBall hρRp hl hq0 hc.le hcρ
    intro p hp t ht
    exact hΨ.range p (closedBall_subset_closedBall hρr.le hp) t (Ioo_subset_Icc_self (htime ht))
  have hSW : closedBall (x₀, (0 : ℝ)) R ⊆ W ×ˢ univ := by
    intro p hp
    refine ⟨hRW ?_, mem_univ _⟩
    exact (show dist p.1 x₀ ≤ dist p (x₀, 0) by
      rw [Prod.dist_eq]; exact le_max_left _ _).trans hp
  let A : ℝ := (max 1 |l⁻¹|) ^ m
  have hA : 0 < A := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  obtain ⟨δ, hδ, hstable⟩ := exists_cNorm_spatial_flow_sub_lt
    (isCompact_closedBall (x₀, (0 : ℝ)) ρ) isOpen_ball (closedBall_subset_ball hρRp)
    (isCompact_closedBall (x₀, (0 : ℝ)) R) (convex_closedBall (x₀, (0 : ℝ)) R)
    (hW.prod isOpen_univ) hSW zero_lt_one hq (TimeRescaling.contDiffOn_field hV₀ l c)
    (TimeRescaling.contDiffOn_flow hl hq0 (hsmooth hΨ₀)) (hode hΨ₀) (hrange hΨ₀)
    m (div_pos hε hA)
  obtain ⟨C, hC, hfield⟩ := TimeRescaling.exists_cNorm_field_sub_bound x₀ hR l c m
  refine ⟨δ / C, div_pos hδ hC, ?_⟩
  intro V Ψ hV hΨ hsmall
  have hfsmall : cNorm (closedBall (x₀, (0 : ℝ)) R) m
      (TimeRescaling.field l c V - TimeRescaling.field l c V₀) < δ := by
    apply (hfield V V₀ W hW hRW hV hV₀).trans_lt
    have := (lt_div_iff₀ hC).mp hsmall
    linarith
  have hinit : ∀ p ∈ ball (x₀, (0 : ℝ)) Rp,
      TimeRescaling.flow 0 l c Ψ (p, 0) = TimeRescaling.flow 0 l c Ψ₀ (p, 0) := by
    intro p hp
    have hp₁ : p.1 ∈ closedBall x₀ r := by
      apply ball_subset_closedBall
      apply ball_subset_ball hRpr.le
      exact (show dist p.1 x₀ ≤ dist p (x₀, 0) by
        rw [Prod.dist_eq]; exact le_max_left _ _).trans_lt hp
    simp only [TimeRescaling.flow, mul_zero, add_zero, hΨ.initial _ hp₁, hΨ₀.initial _ hp₁]
  have haux := hstable (TimeRescaling.field l c V) (TimeRescaling.flow 0 l c Ψ)
    (TimeRescaling.contDiffOn_field hV l c)
    (TimeRescaling.contDiffOn_flow hl hq0 (hsmooth hΨ))
    (hode hΨ) (hrange hΨ) hinit hfsmall 1 (by constructor <;> norm_num)
  have hrec := TimeRescaling.cNorm_flow_sub_recover_le x₀ hρ hρRp hq hl 0 c m
    (hsmooth hΨ) (hsmooth hΨ₀)
  simp only [zero_sub, zero_add, hlρ] at hrec
  apply hrec.trans_lt
  exact (mul_lt_mul_of_pos_left haux hA).trans_eq (mul_div_cancel₀ ε hA.ne')
/-- `app:lem:common-hamilton-phase`: every actual flow is continuous in the
order-`m` field seminorm on each fixed compact inner joint cylinder. The scalar
threshold is chosen before the perturbed field and flow. No derivative of the
perturbation above `m`, or quantitative flow-derivative assumption, occurs.
This supplies the flow input to the parent Hamilton-phase construction's
composition with its varying initial section. -/
theorem exists_cNorm_flow_sub_lt
    {W : Set E} {x₀ : E} {R r T ρ τ : ℝ} {V₀ : E → E} {Ψ₀ : E × ℝ → E}
    (hW : IsOpen W) (hRW : closedBall x₀ R ⊆ W)
    (hV₀ : ContDiffOn ℝ ∞ V₀ W) (hΨ₀ : IsSmoothFlowOn V₀ x₀ R r T Ψ₀)
    (hρ : 0 < ρ) (hρr : ρ < r) (hτ : 0 < τ) (hτT : τ < T)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (V : E → E) (Ψ : E × ℝ → E),
      ContDiffOn ℝ ∞ V W → IsSmoothFlowOn V x₀ R r T Ψ →
      cNorm (closedBall x₀ R) m (V - V₀) < δ →
      cNorm (closedBall x₀ ρ ×ˢ Icc (-τ) τ) m (Ψ - Ψ₀) < ε := by
  by_cases hR : 0 < R
  · exact exists_cNorm_flow_sub_lt_of_radius_pos hW hR hRW hV₀ hΨ₀
      hρ hρr hτ hτT m hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro V Ψ _ hΨ _
  have hval {V : E → E} {Ψ : E × ℝ → E} (hΨ : IsSmoothFlowOn V x₀ R r T Ψ)
      {y : E × ℝ} (hy : y ∈ ball x₀ r ×ˢ Ioo (-T) T) : Ψ y = x₀ := by
    apply dist_le_zero.mp
    exact (hΨ.range y.1 (ball_subset_closedBall hy.1) y.2
      (Ioo_subset_Icc_self hy.2)).trans (le_of_not_gt hR)
  have heq : ∀ z ∈ closedBall x₀ ρ ×ˢ Icc (-τ) τ,
      Ψ - Ψ₀ =ᶠ[𝓝 z] (0 : E × ℝ → E) := by
    intro z hz
    have hz' : z ∈ ball x₀ r ×ˢ Ioo (-T) T :=
      ⟨closedBall_subset_ball hρr hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    filter_upwards [(isOpen_ball.prod isOpen_Ioo).mem_nhds hz'] with y hy
    simp only [Pi.sub_apply, hval hΨ hy, hval hΨ₀ hy, sub_self, Pi.zero_apply]
  rw [GeometricProfile.cNorm_eq_of_eventuallyEq heq m, cNorm_zero]
  exact hε
end JanetCartan.ODE
