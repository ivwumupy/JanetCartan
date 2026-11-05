module

public import JanetCartan.Analysis.ODE.SmoothDependence.FirstDerivative
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Quantitative comparison of flows on a common domain

For `app:lem:common-hamilton-phase`, subtract the trajectory and variational
IVPs on an unordered time segment. Grönwall bounds the trajectory difference,
the reference variation, and then the variation difference. The ODE supplies
the time component of the full joint derivative.

`exists_uniform_flow_comparison` is the conditional comparison input consumed
by `Analysis/ODE/FlowStability`. Its hypotheses are properties of already
constructed flows and pointwise bounds on the fields. It assumes neither flow
closeness nor a bound on the flow derivatives, and asserts no flow existence.
-/

@[expose] public section

open Set Metric
open scoped Topology NNReal

namespace JanetCartan.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private theorem field_difference_le {F : Type*} [NormedAddCommGroup F]
    {V V₀ : E → F} {S : Set E} {K : ℝ≥0} {ε : ℝ}
    (hlip : LipschitzOnWith K V₀ S) (hclose : ∀ y ∈ S, ‖V y - V₀ y‖ ≤ ε)
    {y y₀ : E} (hy : y ∈ S) (hy₀ : y₀ ∈ S) :
    ‖V y - V₀ y₀‖ ≤ (K : ℝ) * ‖y - y₀‖ + ε := by
  calc
    ‖V y - V₀ y₀‖ ≤ ‖V y - V₀ y‖ + ‖V₀ y - V₀ y₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε + (K : ℝ) * ‖y - y₀‖ :=
      add_le_add (hclose y hy) (hlip.norm_sub_le hy hy₀)
    _ = _ := add_comm _ _

private theorem trajectory_difference_le
    {V V₀ : E → E} {u u₀ : ℝ → E} {S : Set E} {K : ℝ≥0} {T ε t : ℝ}
    (hT : 0 < T) (hK : 0 < K) (hε : 0 ≤ ε) (ht : t ∈ Ioo (-T) T)
    (hlip : LipschitzOnWith K V₀ S) (hclose : ∀ y ∈ S, ‖V y - V₀ y‖ ≤ ε)
    (hrange : ∀ τ ∈ Ioo (-T) T, u τ ∈ S)
    (hrange₀ : ∀ τ ∈ Ioo (-T) T, u₀ τ ∈ S)
    (hode : ∀ τ ∈ Ioo (-T) T, HasDerivAt u (V (u τ)) τ)
    (hode₀ : ∀ τ ∈ Ioo (-T) T, HasDerivAt u₀ (V₀ (u₀ τ)) τ)
    (hinit : u 0 = u₀ 0) :
    ‖u t - u₀ t‖ ≤ ((Real.exp ((K : ℝ) * T) - 1) / K) * ε := by
  have hsub : uIcc 0 t ⊆ Ioo (-T) T :=
    ordConnected_Ioo.uIcc_subset ⟨by linarith, hT⟩ ht
  have hg := norm_le_gronwallBound_of_hasDerivAt_uIcc
    (R := fun τ ↦ u τ - u₀ τ) (R' := fun τ ↦ V (u τ) - V₀ (u₀ τ))
    (fun τ hτ ↦ (hode τ (hsub hτ)).sub (hode₀ τ (hsub hτ)))
    (δ := 0) (by simp [hinit])
    (fun τ hτ ↦ field_difference_le hlip hclose (hrange τ (hsub hτ))
      (hrange₀ τ (hsub hτ)))
  have htime : |t - 0| ≤ T := by rw [sub_zero]; exact (abs_lt.mpr ht).le
  apply (hg.trans (gronwallBound_mono le_rfl hε K.coe_nonneg htime)).trans_eq
  rw [gronwallBound_of_K_ne_0 (ne_of_gt (show (0 : ℝ) < K from hK))]
  ring

private theorem variation_norm_le
    {A J : ℝ → E →L[ℝ] E} {K : ℝ≥0} {T t : ℝ}
    (hT : 0 < T) (ht : t ∈ Ioo (-T) T)
    (hA : ∀ τ ∈ Ioo (-T) T, ‖A τ‖ ≤ K)
    (hJ : ∀ τ ∈ Ioo (-T) T, HasDerivAt J ((A τ).comp (J τ)) τ)
    (hinit : J 0 = ContinuousLinearMap.id ℝ E) :
    ‖J t‖ ≤ Real.exp ((K : ℝ) * T) := by
  have hsub : uIcc 0 t ⊆ Ioo (-T) T :=
    ordConnected_Ioo.uIcc_subset ⟨by linarith, hT⟩ ht
  have hg := norm_le_gronwallBound_of_hasDerivAt_uIcc
    (fun τ hτ ↦ hJ τ (hsub hτ))
    (δ := 1) (by rw [hinit]; exact ContinuousLinearMap.norm_id_le)
    (L := K) (ε := 0) (fun τ hτ ↦ by
      simpa using ((A τ).opNorm_comp_le (J τ)).trans
        (mul_le_mul_of_nonneg_right (hA τ (hsub hτ)) (norm_nonneg _)))
  have htime : |t - 0| ≤ T := by rw [sub_zero]; exact (abs_lt.mpr ht).le
  simpa only [gronwallBound_ε0, one_mul] using
    hg.trans (gronwallBound_mono (by norm_num) le_rfl K.coe_nonneg htime)

private theorem joint_derivative_apply {Φ : E × ℝ → E} {x : E} {t : ℝ} {v : E}
    (hd : DifferentiableAt ℝ Φ (x, t))
    (ht : HasDerivAt (fun τ ↦ Φ (x, τ)) v t) (p : E × ℝ) :
    fderiv ℝ Φ (x, t) p = flowInitialDerivative Φ x t p.1 + p.2 • v := by
  have hx : flowInitialDerivative Φ x t =
      (fderiv ℝ Φ (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ) :=
    (hd.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x))).fderiv
  have hv : fderiv ℝ Φ (x, t) (0, 1) = v :=
    (hd.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))).unique ht
  have hp : p = (p.1, 0) + p.2 • (0, (1 : ℝ)) := by ext <;> simp
  rw [hp, map_add, map_smul, hv]
  simp [hx]

private theorem joint_derivative_difference_le
    {Φ Φ₀ : E × ℝ → E} {x : E} {t : ℝ} {v v₀ : E}
    (hd : DifferentiableAt ℝ Φ (x, t)) (hd₀ : DifferentiableAt ℝ Φ₀ (x, t))
    (ht : HasDerivAt (fun τ ↦ Φ (x, τ)) v t)
    (ht₀ : HasDerivAt (fun τ ↦ Φ₀ (x, τ)) v₀ t) :
    ‖fderiv ℝ Φ (x, t) - fderiv ℝ Φ₀ (x, t)‖ ≤
      ‖flowInitialDerivative Φ x t - flowInitialDerivative Φ₀ x t‖ + ‖v - v₀‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro p
  have heq : (fderiv ℝ Φ (x, t) - fderiv ℝ Φ₀ (x, t)) p =
      (flowInitialDerivative Φ x t - flowInitialDerivative Φ₀ x t) p.1 +
        p.2 • (v - v₀) := by
    simp only [sub_apply, joint_derivative_apply hd ht,
      joint_derivative_apply hd₀ ht₀, smul_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖(flowInitialDerivative Φ x t - flowInitialDerivative Φ₀ x t) p.1‖ +
        ‖p.2 • (v - v₀)‖ := norm_add_le _ _
    _ ≤ ‖flowInitialDerivative Φ x t - flowInitialDerivative Φ₀ x t‖ * ‖p.1‖ +
        ‖p.2‖ * ‖v - v₀‖ := by
      rw [norm_smul]; exact add_le_add (ContinuousLinearMap.le_opNorm _ _) le_rfl
    _ ≤ ‖flowInitialDerivative Φ x t - flowInitialDerivative Φ₀ x t‖ * ‖p‖ +
        ‖p‖ * ‖v - v₀‖ := by
      gcongr
      · exact norm_fst_le p
      · exact norm_snd_le p
    _ = _ := by ring

/-- `app:lem:common-hamilton-phase`: quantitative `C⁰` and full joint `C¹`
comparison of two already constructed flows, from the actual ODE and variational
IVPs. The constant is chosen before either field, either flow, or the error.
One possible constant is `G + B * M * G + B + 1`, where
`G = (exp (K * T) - 1) / K`, `M = exp (K * T)`, and `B = 1 + K * G`.
This is the comparison input to the common-domain construction in
`FlowStability`; it asserts no flow existence. -/
theorem exists_uniform_flow_comparison [FiniteDimensional ℝ E]
    (x₀ : E) {R r T : ℝ} (_hR : 0 < R) (hr : 0 < r) (hT : 0 < T)
    {K : ℝ≥0} (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V V₀ : E → E) (Ψ Ψ₀ : E × ℝ → E) (ε : ℝ),
      LipschitzOnWith K V₀ (closedBall x₀ R) →
      LipschitzOnWith K (fderiv ℝ V₀) (closedBall x₀ R) →
      (∀ y ∈ closedBall x₀ R, ‖fderiv ℝ V y‖ ≤ K) →
      (∀ y ∈ closedBall x₀ R, ‖fderiv ℝ V₀ y‖ ≤ K) →
      0 ≤ ε →
      (∀ y ∈ closedBall x₀ R, ‖V y - V₀ y‖ ≤ ε) →
      (∀ y ∈ closedBall x₀ R, ‖fderiv ℝ V y - fderiv ℝ V₀ y‖ ≤ ε) →
      ContDiffOn ℝ 1 Ψ (ball x₀ r ×ˢ Ioo (-T) T) →
      ContDiffOn ℝ 1 Ψ₀ (ball x₀ r ×ˢ Ioo (-T) T) →
      (∀ x ∈ ball x₀ r, Ψ (x, 0) = x) →
      (∀ x ∈ ball x₀ r, Ψ₀ (x, 0) = x) →
      (∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-T) T, Ψ (x, t) ∈ closedBall x₀ R) →
      (∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-T) T, Ψ₀ (x, t) ∈ closedBall x₀ R) →
      (∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-T) T,
        HasDerivAt (fun s ↦ Ψ (x, s)) (V (Ψ (x, t))) t) →
      (∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-T) T,
        HasDerivAt (fun s ↦ Ψ₀ (x, s)) (V₀ (Ψ₀ (x, t))) t) →
      (∀ x ∈ ball x₀ r, flowInitialDerivative Ψ x 0 = ContinuousLinearMap.id ℝ E) →
      (∀ x ∈ ball x₀ r, flowInitialDerivative Ψ₀ x 0 = ContinuousLinearMap.id ℝ E) →
      (∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-T) T,
        HasDerivAt (flowInitialDerivative Ψ x)
          ((fderiv ℝ V (Ψ (x, t))).comp (flowInitialDerivative Ψ x t)) t) →
      (∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-T) T,
        HasDerivAt (flowInitialDerivative Ψ₀ x)
          ((fderiv ℝ V₀ (Ψ₀ (x, t))).comp (flowInitialDerivative Ψ₀ x t)) t) →
      ∀ z ∈ closedBall x₀ (r / 2) ×ˢ Icc (-T / 2) (T / 2),
        ‖Ψ z - Ψ₀ z‖ ≤ C * ε ∧ ‖fderiv ℝ Ψ z - fderiv ℝ Ψ₀ z‖ ≤ C * ε := by
  let G := (Real.exp ((K : ℝ) * T) - 1) / K
  let M := Real.exp ((K : ℝ) * T)
  let B := 1 + (K : ℝ) * G
  have hG : 0 ≤ G := div_nonneg
    (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg K.coe_nonneg hT.le))) K.coe_nonneg
  have hM : 0 < M := Real.exp_pos _
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨G + B * M * G + B + 1, by positivity, ?_⟩
  intro V V₀ Ψ Ψ₀ ε hlip hDlip hDV hDV₀ hε hclose hDclose hΨ hΨ₀
    hi hi₀ hrange hrange₀ hode hode₀ hJi hJi₀ hJ hJ₀
  have htraj (x : E) (hx : x ∈ ball x₀ r) (t : ℝ) (ht : t ∈ Ioo (-T) T) :
      ‖Ψ (x, t) - Ψ₀ (x, t)‖ ≤ G * ε :=
    trajectory_difference_le hT hK hε ht hlip hclose (hrange x hx) (hrange₀ x hx)
      (hode x hx) (hode₀ x hx) (by rw [hi x hx, hi₀ x hx])
  have hfield (x : E) (hx : x ∈ ball x₀ r) (t : ℝ) (ht : t ∈ Ioo (-T) T) :
      ‖V (Ψ (x, t)) - V₀ (Ψ₀ (x, t))‖ ≤ B * ε := by
    calc
      _ ≤ (K : ℝ) * ‖Ψ (x, t) - Ψ₀ (x, t)‖ + ε :=
        field_difference_le hlip hclose (hrange x hx t ht) (hrange₀ x hx t ht)
      _ ≤ (K : ℝ) * (G * ε) + ε := by gcongr; exact htraj x hx t ht
      _ = B * ε := by dsimp [B]; ring
  have hcoeff (x : E) (hx : x ∈ ball x₀ r) (t : ℝ) (ht : t ∈ Ioo (-T) T) :
      ‖fderiv ℝ V (Ψ (x, t)) - fderiv ℝ V₀ (Ψ₀ (x, t))‖ ≤ B * ε := by
    calc
      _ ≤ (K : ℝ) * ‖Ψ (x, t) - Ψ₀ (x, t)‖ + ε :=
        field_difference_le hDlip hDclose (hrange x hx t ht) (hrange₀ x hx t ht)
      _ ≤ (K : ℝ) * (G * ε) + ε := by gcongr; exact htraj x hx t ht
      _ = B * ε := by dsimp [B]; ring
  have hJbound (x : E) (hx : x ∈ ball x₀ r) (t : ℝ) (ht : t ∈ Ioo (-T) T) :
      ‖flowInitialDerivative Ψ₀ x t‖ ≤ M :=
    variation_norm_le hT ht (fun τ hτ ↦ hDV₀ _ (hrange₀ x hx τ hτ))
      (hJ₀ x hx) (hJi₀ x hx)
  have hJdiff (x : E) (hx : x ∈ ball x₀ r) (t : ℝ) (ht : t ∈ Ioo (-T) T) :
      ‖flowInitialDerivative Ψ x t - flowInitialDerivative Ψ₀ x t‖ ≤ (B * M * G) * ε := by
    have hsub : uIcc 0 t ⊆ Ioo (-T) T :=
      ordConnected_Ioo.uIcc_subset ⟨by linarith, hT⟩ ht
    have hg := linearEvolution_dist_le_gronwallBound
      (fun τ hτ ↦ hJ x hx τ (hsub hτ)) (fun τ hτ ↦ hJ₀ x hx τ (hsub hτ))
      (by rw [hJi x hx, hJi₀ x hx])
      (fun τ hτ ↦ hDV _ (hrange x hx τ (hsub hτ)))
      (fun τ hτ ↦ hcoeff x hx τ (hsub hτ))
      (fun τ hτ ↦ hJbound x hx τ (hsub hτ)) (mul_nonneg hB.le hε)
    rw [dist_eq_norm] at hg
    have htime : |t - 0| ≤ T := by rw [sub_zero]; exact (abs_lt.mpr ht).le
    apply (hg.trans (gronwallBound_mono le_rfl (by positivity) K.coe_nonneg htime)).trans_eq
    rw [gronwallBound_of_K_ne_0 (ne_of_gt (show (0 : ℝ) < K from hK))]
    dsimp [G, M]
    ring
  intro z hz
  have hx : z.1 ∈ ball x₀ r :=
    (closedBall_subset_ball (by linarith : r / 2 < r)) hz.1
  have ht : z.2 ∈ Ioo (-T) T := by constructor <;> linarith [hz.2.1, hz.2.2]
  have hd : DifferentiableAt ℝ Ψ z :=
    (hΨ.differentiableOn (by simp)).differentiableAt
      ((isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hx, ht⟩)
  have hd₀ : DifferentiableAt ℝ Ψ₀ z :=
    (hΨ₀.differentiableOn (by simp)).differentiableAt
      ((isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hx, ht⟩)
  constructor
  · exact (htraj z.1 hx z.2 ht).trans (mul_le_mul_of_nonneg_right
      (by nlinarith [mul_nonneg (mul_nonneg hB.le hM.le) hG]) hε)
  · calc
      _ ≤ ‖flowInitialDerivative Ψ z.1 z.2 - flowInitialDerivative Ψ₀ z.1 z.2‖ +
          ‖V (Ψ z) - V₀ (Ψ₀ z)‖ :=
        joint_derivative_difference_le hd hd₀ (hode z.1 hx z.2 ht) (hode₀ z.1 hx z.2 ht)
      _ ≤ (B * M * G) * ε + B * ε :=
        add_le_add (hJdiff z.1 hx z.2 ht) (hfield z.1 hx z.2 ht)
      _ ≤ (G + B * M * G + B + 1) * ε := by nlinarith [mul_nonneg hG hε]

end JanetCartan.ODE

