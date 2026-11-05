module

public import JanetCartan.Analysis.ODE.FlowStability
public import JanetCartan.Analysis.ODE.DerivativeBounds.Gronwall

/-!
# Trajectory comparison and uniqueness on the common cylinder

The order-zero step of the differentiated ODE comparison in
`app:lem:common-hamilton-phase`. Only the reference field needs a Lipschitz
bound. The perturbation is measured in order zero. Uniqueness applies to any
actual flows, including independently chosen common-flow constructions.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology NNReal

namespace JanetCartan.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:lem:common-hamilton-phase`: the order-zero comparison for arbitrary
trajectories with the same initial value, in either time direction. This is the
base case for spatial-jet stability; no derivative of the perturbation occurs. -/
theorem norm_trajectory_sub_le_gronwall
    {V V₀ : E → E} {u u₀ : ℝ → E} {S : Set E} {K : ℝ≥0} {T ε t : ℝ}
    (hT : 0 < T) (hε : 0 ≤ ε) (ht : t ∈ Ioo (-T) T)
    (hlip : LipschitzOnWith K V₀ S)
    (hclose : ∀ y ∈ S, ‖V y - V₀ y‖ ≤ ε)
    (hrange : ∀ τ ∈ Ioo (-T) T, u τ ∈ S)
    (hrange₀ : ∀ τ ∈ Ioo (-T) T, u₀ τ ∈ S)
    (hode : ∀ τ ∈ Ioo (-T) T, HasDerivAt u (V (u τ)) τ)
    (hode₀ : ∀ τ ∈ Ioo (-T) T, HasDerivAt u₀ (V₀ (u₀ τ)) τ)
    (hinit : u 0 = u₀ 0) :
    ‖u t - u₀ t‖ ≤ gronwallBound 0 K 1 T * ε := by
  have hsub : uIcc 0 t ⊆ Ioo (-T) T :=
    ordConnected_Ioo.uIcc_subset ⟨by linarith, hT⟩ ht
  have hg := norm_le_gronwallBound_of_hasDerivAt_uIcc
    (R := fun τ ↦ u τ - u₀ τ) (R' := fun τ ↦ V (u τ) - V₀ (u₀ τ))
    (fun τ hτ ↦ (hode τ (hsub hτ)).sub (hode₀ τ (hsub hτ)))
    (δ := 0) (by simp [hinit])
    (L := K) (ε := ε) (fun τ hτ ↦ by
      calc
        _ ≤ ‖V (u τ) - V₀ (u τ)‖ + ‖V₀ (u τ) - V₀ (u₀ τ)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ε + (K : ℝ) * ‖u τ - u₀ τ‖ := add_le_add
          (hclose _ (hrange τ (hsub hτ)))
          (hlip.norm_sub_le (hrange τ (hsub hτ)) (hrange₀ τ (hsub hτ)))
        _ = _ := add_comm _ _)
  have htime : |t - 0| ≤ T := by simpa using (abs_lt.mpr ht).le
  apply (hg.trans (gronwallBound_mono le_rfl hε K.coe_nonneg htime)).trans_eq
  simpa using gronwallBound_mul 0 K 1 ε T

/-- `app:lem:common-hamilton-phase`: two actual flows of one Lipschitz field
agree on the entire closed cylinder. This identifies different choices in the
common-flow existence construction, without assuming derivative equality. -/
theorem IsSmoothFlowOn.eqOn_of_lipschitz
    {V : E → E} {x₀ : E} {R r T : ℝ} {Ψ Ψ₀ : E × ℝ → E} {K : ℝ≥0}
    (hΨ : IsSmoothFlowOn V x₀ R r T Ψ)
    (hΨ₀ : IsSmoothFlowOn V x₀ R r T Ψ₀)
    (hT : 0 < T) (hlip : LipschitzOnWith K V (closedBall x₀ R)) :
    EqOn Ψ Ψ₀ (closedBall x₀ r ×ˢ Icc (-T) T) := by
  intro z hz
  have heq : EqOn (fun t ↦ Ψ (z.1, t)) (fun t ↦ Ψ₀ (z.1, t)) (Ioo (-T) T) := by
    intro t ht
    have hb := norm_trajectory_sub_le_gronwall hT (le_refl 0) ht hlip
      (fun _ _ ↦ by simp)
      (fun τ hτ ↦ hΨ.range _ hz.1 τ (Ioo_subset_Icc_self hτ))
      (fun τ hτ ↦ hΨ₀.range _ hz.1 τ (Ioo_subset_Icc_self hτ))
      (fun _ hτ ↦ hΨ.hasDerivAt hz.1 hτ)
      (fun _ hτ ↦ hΨ₀.hasDerivAt hz.1 hτ)
      (by rw [hΨ.initial _ hz.1, hΨ₀.initial _ hz.1])
    simpa only [mul_zero, norm_le_zero_iff, sub_eq_zero] using hb
  have hc : ContinuousOn (fun t ↦ Ψ (z.1, t)) (Icc (-T) T) :=
    hΨ.continuous.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht ↦ ⟨hz.1, ht⟩)
  have hc₀ : ContinuousOn (fun t ↦ Ψ₀ (z.1, t)) (Icc (-T) T) :=
    hΨ₀.continuous.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht ↦ ⟨hz.1, ht⟩)
  exact heq.of_subset_closure hc hc₀ Ioo_subset_Icc_self
    (by rw [closure_Ioo (by linarith : -T ≠ T)]) hz.2

/-- `app:lem:common-hamilton-phase`: smoothness of the field near the compact
range ball supplies the Lipschitz hypothesis in flow uniqueness. -/
theorem IsSmoothFlowOn.eqOn [FiniteDimensional ℝ E]
    {V : E → E} {U : Set E} {x₀ : E} {R r T : ℝ} {Ψ Ψ₀ : E × ℝ → E}
    (hΨ : IsSmoothFlowOn V x₀ R r T Ψ)
    (hΨ₀ : IsSmoothFlowOn V x₀ R r T Ψ₀)
    (hT : 0 < T) (hU : IsOpen U) (hRU : closedBall x₀ R ⊆ U)
    (hV : ContDiffOn ℝ ∞ V U) :
    EqOn Ψ Ψ₀ (closedBall x₀ r ×ˢ Icc (-T) T) := by
  let K : ℝ≥0 := ⟨cNorm (closedBall x₀ R) 2 V, cNorm_nonneg _ _ _⟩
  exact hΨ.eqOn_of_lipschitz hΨ₀ hT
    (field_and_fderiv_lipschitzOnWith_of_cNorm (K := K) hU hRU hV le_rfl).1

/-- `app:lem:common-hamilton-phase`: uniqueness also identifies every ambient
joint jet on the open cylinder. The parent may therefore change the chosen
common flow before composing with the initial section. -/
theorem IsSmoothFlowOn.iteratedFDeriv_eq [FiniteDimensional ℝ E]
    {V : E → E} {U : Set E} {x₀ : E} {R r T : ℝ} {Ψ Ψ₀ : E × ℝ → E}
    (hΨ : IsSmoothFlowOn V x₀ R r T Ψ)
    (hΨ₀ : IsSmoothFlowOn V x₀ R r T Ψ₀)
    (hT : 0 < T) (hU : IsOpen U) (hRU : closedBall x₀ R ⊆ U)
    (hV : ContDiffOn ℝ ∞ V U) (m : ℕ)
    {z : E × ℝ} (hz : z ∈ ball x₀ r ×ˢ Ioo (-T) T) :
    iteratedFDeriv ℝ m Ψ z = iteratedFDeriv ℝ m Ψ₀ z := by
  have heq : Ψ =ᶠ[𝓝 z] Ψ₀ := by
    filter_upwards [(isOpen_ball.prod isOpen_Ioo).mem_nhds hz] with y hy
    exact hΨ.eqOn hΨ₀ hT hU hRU hV
      ⟨ball_subset_closedBall hy.1, Ioo_subset_Icc_self hy.2⟩
  exact (heq.iteratedFDeriv ℝ m).eq_of_nhds

/-- `app:lem:common-hamilton-phase`: uniform `C⁰` continuity of any actual
flows on a fixed inner cylinder, measured by the field's `C⁰` seminorm alone.
This supplies the base case of finite-order flow continuity. -/
theorem exists_cNorm_zero_flow_sub_lt [FiniteDimensional ℝ E]
    {U : Set E} {x₀ : E} {R r T r' T' : ℝ} {V₀ : E → E}
    (hU : IsOpen U) (hRU : closedBall x₀ R ⊆ U)
    (hV₀ : ContDiffOn ℝ ∞ V₀ U) (hT : 0 < T)
    (hr' : r' ≤ r) (hT' : T' < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (V : E → E) (Ψ Ψ₀ : E × ℝ → E),
      ContDiffOn ℝ ∞ V U → IsSmoothFlowOn V x₀ R r T Ψ →
      IsSmoothFlowOn V₀ x₀ R r T Ψ₀ →
      cNorm (closedBall x₀ R) 0 (V - V₀) < δ →
      cNorm (closedBall x₀ r' ×ˢ Icc (-T') T') 0 (Ψ - Ψ₀) < ε := by
  let K : ℝ≥0 := ⟨cNorm (closedBall x₀ R) 2 V₀, cNorm_nonneg _ _ _⟩
  let C := gronwallBound 0 K 1 T
  have hC : 0 ≤ C := gronwallBound_nonneg le_rfl K.coe_nonneg zero_le_one hT.le
  have hlip := (field_and_fderiv_lipschitzOnWith_of_cNorm
    (K := K) hU hRU hV₀ le_rfl).1
  refine ⟨ε / (C + 1), div_pos hε (by positivity), ?_⟩
  intro V Ψ Ψ₀ hV hΨ hΨ₀ hsmall
  let e := cNorm (closedBall x₀ R) 0 (V - V₀)
  have he : 0 ≤ e := cNorm_nonneg _ _ _
  have hb : cNorm (closedBall x₀ r' ×ˢ Icc (-T') T') 0 (Ψ - Ψ₀) ≤ C * e := by
    apply (cNorm_le_sum_of_bounds (C := fun _ ↦ C * e)
      (fun _ _ ↦ mul_nonneg hC he) ?_).trans_eq (by simp)
    intro j hj z hz
    have hj0 : j = 0 := by omega
    subst j
    rw [norm_iteratedFDeriv_zero]
    have hx := closedBall_subset_closedBall hr' hz.1
    have ht : z.2 ∈ Ioo (-T) T := ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
    exact norm_trajectory_sub_le_gronwall hT he ht hlip
      (fun y hy ↦ by
        simpa only [e, norm_iteratedFDeriv_zero, Pi.sub_apply] using
          norm_iteratedFDeriv_le_cNorm_of_contDiffAt (f := V - V₀) (isCompact_closedBall x₀ R)
            (fun w hw ↦ ((hV.sub hV₀).contDiffAt (hU.mem_nhds (hRU hw))).of_le
              (by simp)) hy (le_refl 0))
      (fun τ hτ ↦ hΨ.range _ hx τ (Ioo_subset_Icc_self hτ))
      (fun τ hτ ↦ hΨ₀.range _ hx τ (Ioo_subset_Icc_self hτ))
      (fun _ hτ ↦ hΨ.hasDerivAt hx hτ)
      (fun _ hτ ↦ hΨ₀.hasDerivAt hx hτ)
      (by rw [hΨ.initial _ hx, hΨ₀.initial _ hx])
  apply hb.trans_lt
  have h := (lt_div_iff₀ (by positivity : 0 < C + 1)).mp hsmall
  change e * (C + 1) < ε at h
  nlinarith

end JanetCartan.ODE
