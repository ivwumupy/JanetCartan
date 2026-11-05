module

public import JanetCartan.Analysis.ODE.SmoothDependence.SmoothFlow
public import JanetCartan.Analysis.ODE.FlowStability.Comparison
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Common domains for perturbations of smooth vector fields

The construction for `app:lem:common-hamilton-phase` uses fixed bounds on a
closed ball to choose the initial radius and the two-sided time interval before
choosing the perturbed field. Picard–Lindelöf supplies the trajectories, and
smooth dependence identifies their actual initial-data derivatives.
`exists_common_smoothFlowOn_with_cNorm_stability` combines this construction
with Grönwall comparison to give uniform `C⁰` and full joint `C¹` stability
from the field's `C²` seminorm alone. It is the ODE input to the Hamilton-field
perturbation construction in `HamiltonPhase/SymbolStability`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped Topology NNReal ContDiff

namespace JanetCartan.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:lem:common-hamilton-phase`: the properties retained by the common-domain
flow construction. The variational derivative is the actual derivative in the
initial point, and the ODE also holds within the closed time interval. -/
structure IsSmoothFlowOn (V : E → E) (x₀ : E) (R r T : ℝ)
    (Ψ : E × ℝ → E) : Prop where
  initial : ∀ x ∈ closedBall x₀ r, Ψ (x, 0) = x
  ode : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc (-T) T,
    HasDerivWithinAt (fun s ↦ Ψ (x, s)) (V (Ψ (x, t))) (Icc (-T) T) t
  range : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc (-T) T,
    Ψ (x, t) ∈ closedBall x₀ R
  continuous : ContinuousOn Ψ (closedBall x₀ r ×ˢ Icc (-T) T)
  smooth : ContDiffOn ℝ ∞ Ψ (ball x₀ r ×ˢ Ioo (-T) T)
  variation_initial : ∀ x ∈ ball x₀ r,
    flowInitialDerivative Ψ x 0 = ContinuousLinearMap.id ℝ E
  variation : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-T) T,
    HasDerivAt (flowInitialDerivative Ψ x)
      ((fderiv ℝ V (Ψ (x, t))).comp (flowInitialDerivative Ψ x t)) t

/-- `app:lem:common-hamilton-phase`: on the open time interval the constructed
flow solves the ordinary, ambient ODE. -/
theorem IsSmoothFlowOn.hasDerivAt {V : E → E} {x₀ : E} {R r T : ℝ}
    {Ψ : E × ℝ → E} (hΨ : IsSmoothFlowOn V x₀ R r T Ψ)
    {x : E} (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo (-T) T) :
    HasDerivAt (fun s ↦ Ψ (x, s)) (V (Ψ (x, t))) t :=
  (hΨ.ode x hx t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- `app:lem:common-hamilton-phase`: upgrade a Picard–Lindelöf construction on
a prescribed closed cylinder, preserving its radius and time interval. This is
the fixed-domain input to the uniform perturbation construction below. -/
theorem exists_smoothFlowOn_of_bounds [CompleteSpace E]
    {V : E → E} {U : Set E} {x₀ : E} {R r T : ℝ} {L K : ℝ≥0}
    (hU : IsOpen U) (hRU : closedBall x₀ R ⊆ U)
    (hV : ContDiffOn ℝ ∞ V U) (hR : 0 ≤ R) (hr : 0 ≤ r) (hT : 0 < T)
    (hlip : LipschitzOnWith K V (closedBall x₀ R))
    (hbound : ∀ x ∈ closedBall x₀ R, ‖V x‖ ≤ L)
    (htime : (L : ℝ) * T ≤ R - r) :
    ∃ Ψ : E × ℝ → E, IsSmoothFlowOn V x₀ R r T Ψ := by
  let t₀ : Icc (-T) T := ⟨0, by constructor <;> linarith⟩
  have hpl : IsPicardLindelof (fun _ ↦ V) t₀ x₀ ⟨R, hR⟩ ⟨r, hr⟩ L K :=
    { lipschitzOnWith := fun _ _ ↦ hlip
      continuousOn := fun _ _ ↦ continuousOn_const
      norm_le := fun _ _ ↦ hbound
      mul_max_le := by
        change (L : ℝ) * max (T - 0) (0 - -T) ≤ R - r
        simpa using htime }
  obtain ⟨Ψ, hi, hd, hm, hc, K', hK'⟩ := exists_localFlow_with_range hpl
  have ht₀ : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith, hT⟩
  have hc' := hc.mono (prod_mono ball_subset_closedBall Ioo_subset_Icc_self)
  have hm' : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-T) T, Ψ (x, t) ∈ U :=
    fun x hx t ht ↦ hRU (hm x (ball_subset_closedBall hx) t (Ioo_subset_Icc_self ht))
  have hi' : ∀ x ∈ ball x₀ r, Ψ (x, 0) = x :=
    fun x hx ↦ hi x (ball_subset_closedBall hx)
  have hd' : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-T) T,
      HasDerivAt (fun s ↦ Ψ (x, s)) (V (Ψ (x, t))) t :=
    fun x hx t ht ↦ (hd x (ball_subset_closedBall hx) t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hK'' : ∀ t ∈ Ioo (-T) T, LipschitzOnWith K' (fun x ↦ Ψ (x, t)) (ball x₀ r) :=
    fun t ht ↦ (hK' t (Ioo_subset_Icc_self ht)).mono ball_subset_closedBall
  obtain ⟨_, hJ₀, hJ⟩ := contDiffOn_flow_and_variational_equation hU
    (hV.of_le (by simp)) isOpen_ball ht₀ hc' hm' hi' hd' hK''
  exact ⟨Ψ, hi, hd, hm, hc,
    contDiffOn_localFlow (⊤ : ℕ∞) hU hV isOpen_ball ht₀ hc' hm' hi' hd' hK'', hJ₀, hJ⟩

/-- `app:lem:common-hamilton-phase`: the compact-set `C²` seminorm controls
the field and its first ambient derivative. The pointwise smoothness assumption
allows a field defined smoothly only on a neighborhood of the compact set. -/
theorem norm_and_fderiv_le_cNorm_two {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {f : E → F}
    (hs : IsCompact s) (hf : ∀ x ∈ s, ContDiffAt ℝ 2 f x) {x : E} (hx : x ∈ s) :
    ‖f x‖ ≤ cNorm s 2 f ∧ ‖fderiv ℝ f x‖ ≤ cNorm s 2 f := by
  constructor
  · simpa only [norm_iteratedFDeriv_zero] using
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt hs hf hx (show 0 ≤ 2 by omega)
  · simpa only [norm_iteratedFDeriv_one] using
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt hs hf hx (show 1 ≤ 2 by omega)

/-- `app:lem:common-hamilton-phase`: a `C²` perturbation of size at most one
has common bounds on its value and derivative throughout the prescribed ball.
These are the quantitative inputs to Picard–Lindelöf; no flow is assumed. -/
theorem field_bounds_of_cNorm_sub_le_one [FiniteDimensional ℝ E]
    {U : Set E} {x₀ : E} {R : ℝ} {V V₀ : E → E}
    (hU : IsOpen U) (hRU : closedBall x₀ R ⊆ U)
    (hV : ContDiffOn ℝ ∞ V U) (hV₀ : ContDiffOn ℝ ∞ V₀ U)
    (hsmall : cNorm (closedBall x₀ R) 2 (V - V₀) ≤ 1) :
    ∀ x ∈ closedBall x₀ R,
      ‖V x‖ ≤ cNorm (closedBall x₀ R) 2 V₀ + 1 ∧
      ‖fderiv ℝ V x‖ ≤ cNorm (closedBall x₀ R) 2 V₀ + 1 := by
  have hVat (x) (hx : x ∈ closedBall x₀ R) : ContDiffAt ℝ 2 V x :=
    (hV.contDiffAt (hU.mem_nhds (hRU hx))).of_le (by simp)
  have hV₀at (x) (hx : x ∈ closedBall x₀ R) : ContDiffAt ℝ 2 V₀ x :=
    (hV₀.contDiffAt (hU.mem_nhds (hRU hx))).of_le (by simp)
  intro x hx
  have hb₀ := norm_and_fderiv_le_cNorm_two (isCompact_closedBall x₀ R) hV₀at hx
  have hb := norm_and_fderiv_le_cNorm_two (isCompact_closedBall x₀ R)
    (fun y hy ↦ (hVat y hy).sub (hV₀at y hy)) hx
  have hdV := (hVat x hx).differentiableAt (by norm_num)
  have hdV₀ := (hV₀at x hx).differentiableAt (by norm_num)
  rw [fderiv_fun_sub hdV hdV₀] at hb
  constructor
  · calc
      ‖V x‖ = ‖(V x - V₀ x) + V₀ x‖ := by rw [sub_add_cancel]
      _ ≤ ‖V x - V₀ x‖ + ‖V₀ x‖ := norm_add_le _ _
      _ ≤ cNorm (closedBall x₀ R) 2 V₀ + 1 := by
        have h := hb.1.trans hsmall
        change ‖V x - V₀ x‖ ≤ 1 at h
        linarith [hb₀.1]
  · calc
      ‖fderiv ℝ V x‖ = ‖(fderiv ℝ V x - fderiv ℝ V₀ x) + fderiv ℝ V₀ x‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖fderiv ℝ V x - fderiv ℝ V₀ x‖ + ‖fderiv ℝ V₀ x‖ := norm_add_le _ _
      _ ≤ cNorm (closedBall x₀ R) 2 V₀ + 1 := by linarith [hb.2.trans hsmall, hb₀.2]

/-- `app:lem:common-hamilton-phase`: the reference `C²` seminorm supplies
Lipschitz constants for both the field and its derivative on the range ball.
These bounds control the coefficient difference in the variational equations
when comparing the two common-domain flows. -/
theorem field_and_fderiv_lipschitzOnWith_of_cNorm [FiniteDimensional ℝ E]
    {U : Set E} {x₀ : E} {R : ℝ} {V : E → E} {K : ℝ≥0}
    (hU : IsOpen U) (hRU : closedBall x₀ R ⊆ U)
    (hV : ContDiffOn ℝ ∞ V U) (hK : cNorm (closedBall x₀ R) 2 V ≤ K) :
    LipschitzOnWith K V (closedBall x₀ R) ∧
      LipschitzOnWith K (fderiv ℝ V) (closedBall x₀ R) := by
  have hVat (x) (hx : x ∈ closedBall x₀ R) : ContDiffAt ℝ 2 V x :=
    (hV.contDiffAt (hU.mem_nhds (hRU hx))).of_le (by simp)
  constructor
  · apply (convex_closedBall x₀ R).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x hx ↦ (hVat x hx).differentiableAt (by norm_num))
    intro x hx
    exact_mod_cast ((norm_and_fderiv_le_cNorm_two (isCompact_closedBall x₀ R)
      hVat hx).2.trans hK)
  · have hDV : ContDiffOn ℝ 1 (fderiv ℝ V) U := hV.fderiv_of_isOpen hU (by simp)
    apply (convex_closedBall x₀ R).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x hx ↦ (hDV.contDiffAt
        (hU.mem_nhds (hRU hx))).differentiableAt (by simp))
    intro x hx
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall x₀ R)
      hVat hx (show 2 ≤ 2 from le_rfl)
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at hb
    exact_mod_cast hb.trans hK

/-- `app:lem:common-hamilton-phase`: all smooth fields in a fixed `C²`
neighborhood of the reference field have smooth flows on the same positive
two-sided cylinder. The initial radius is `R/2`, and every trajectory remains
in the original closed ball. This constructs the common flows; quantitative
comparison of those flows is a separate obligation. -/
theorem exists_common_smoothFlowOn [FiniteDimensional ℝ E]
    {U : Set E} {x₀ : E} {R : ℝ} {V₀ : E → E}
    (hU : IsOpen U) (hR : 0 < R) (hRU : closedBall x₀ R ⊆ U)
    (hV₀ : ContDiffOn ℝ ∞ V₀ U) :
    ∃ T > (0 : ℝ), ∃ Ψ₀ : E × ℝ → E,
      IsSmoothFlowOn V₀ x₀ R (R / 2) T Ψ₀ ∧
      ∀ V : E → E, ContDiffOn ℝ ∞ V U →
        cNorm (closedBall x₀ R) 2 (V - V₀) ≤ 1 →
        ∃ Ψ : E × ℝ → E, IsSmoothFlowOn V x₀ R (R / 2) T Ψ := by
  let L : ℝ≥0 := ⟨cNorm (closedBall x₀ R) 2 V₀ + 1,
    add_nonneg (cNorm_nonneg _ _ _) zero_le_one⟩
  have hL : 0 < (L : ℝ) := by
    change 0 < cNorm (closedBall x₀ R) 2 V₀ + 1
    linarith [cNorm_nonneg (closedBall x₀ R) 2 V₀]
  let T := R / (2 * (L : ℝ))
  have hT : 0 < T := div_pos hR (mul_pos (by norm_num) hL)
  have htime : (L : ℝ) * T ≤ R - R / 2 := by
    dsimp [T]
    field_simp
    linarith
  have hex (V : E → E) (hV : ContDiffOn ℝ ∞ V U)
      (hsmall : cNorm (closedBall x₀ R) 2 (V - V₀) ≤ 1) :
      ∃ Ψ : E × ℝ → E, IsSmoothFlowOn V x₀ R (R / 2) T Ψ := by
    have hb := field_bounds_of_cNorm_sub_le_one hU hRU hV hV₀ hsmall
    have hlip : LipschitzOnWith L V (closedBall x₀ R) :=
      (convex_closedBall x₀ R).lipschitzOnWith_of_nnnorm_fderiv_le
        (fun x hx ↦ (hV.contDiffAt (hU.mem_nhds (hRU hx))).differentiableAt (by simp))
        (fun x hx ↦ by exact_mod_cast (hb x hx).2)
    exact exists_smoothFlowOn_of_bounds (L := L) hU hRU hV hR.le (half_pos hR).le hT
      hlip (fun x hx ↦ (hb x hx).1) htime
  obtain ⟨Ψ₀, hΨ₀⟩ := hex V₀ hV₀ (by simp)
  exact ⟨T, hT, Ψ₀, hΨ₀, hex⟩

/-- `app:lem:common-hamilton-phase`: a smooth reference field on a neighborhood
of a closed ball has a fixed positive initial radius, two-sided time interval,
comparison constant, and `C²` perturbation threshold. Every smooth field within
that threshold admits a flow on the same closed cylinder, with the actual ODE
and initial-data variational equation, and uniform value and full joint
derivative differences on the smaller closed cylinder. This supplies the flow
construction and low-order continuity used by `HamiltonPhase/SymbolStability`;
no flow existence or comparison estimate is assumed. We may take `r = R / 2`
and `δ = 1`. -/
theorem exists_common_smoothFlowOn_with_cNorm_stability [FiniteDimensional ℝ E]
    {U : Set E} {x₀ : E} {R : ℝ} {V₀ : E → E}
    (hU : IsOpen U) (hR : 0 < R) (hRU : closedBall x₀ R ⊆ U)
    (hV₀ : ContDiffOn ℝ ∞ V₀ U) :
    ∃ r > (0 : ℝ), ∃ T > (0 : ℝ), ∃ C > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∃ Ψ₀ : E × ℝ → E, IsSmoothFlowOn V₀ x₀ R r T Ψ₀ ∧
        ∀ V : E → E, ContDiffOn ℝ ∞ V U →
          cNorm (closedBall x₀ R) 2 (V - V₀) ≤ δ →
          ∃ Ψ : E × ℝ → E, IsSmoothFlowOn V x₀ R r T Ψ ∧
            ∀ z ∈ closedBall x₀ (r / 2) ×ˢ Icc (-T / 2) (T / 2),
              ‖Ψ z - Ψ₀ z‖ ≤ C * cNorm (closedBall x₀ R) 2 (V - V₀) ∧
              ‖fderiv ℝ Ψ z - fderiv ℝ Ψ₀ z‖ ≤
                C * cNorm (closedBall x₀ R) 2 (V - V₀) := by
  obtain ⟨T, hT, Ψ₀, hΨ₀, hex⟩ := exists_common_smoothFlowOn hU hR hRU hV₀
  let K : ℝ≥0 := ⟨cNorm (closedBall x₀ R) 2 V₀ + 1,
    add_nonneg (cNorm_nonneg _ _ _) zero_le_one⟩
  have hK : 0 < K := by
    change 0 < cNorm (closedBall x₀ R) 2 V₀ + 1
    linarith [cNorm_nonneg (closedBall x₀ R) 2 V₀]
  have hK₀ : cNorm (closedBall x₀ R) 2 V₀ ≤ K := by
    change cNorm (closedBall x₀ R) 2 V₀ ≤ cNorm (closedBall x₀ R) 2 V₀ + 1
    linarith
  obtain ⟨hlip₀, hDlip₀⟩ := field_and_fderiv_lipschitzOnWith_of_cNorm hU hRU hV₀ hK₀
  have hV₀at (x) (hx : x ∈ closedBall x₀ R) : ContDiffAt ℝ 2 V₀ x :=
    (hV₀.contDiffAt (hU.mem_nhds (hRU hx))).of_le (by simp)
  have hDV₀ (x) (hx : x ∈ closedBall x₀ R) : ‖fderiv ℝ V₀ x‖ ≤ K :=
    ((norm_and_fderiv_le_cNorm_two (isCompact_closedBall x₀ R) hV₀at hx).2).trans hK₀
  obtain ⟨C, hC, hcompare⟩ := exists_uniform_flow_comparison x₀ hR (half_pos hR) hT hK
  refine ⟨R / 2, half_pos hR, T, hT, C, hC, 1, zero_lt_one, Ψ₀, hΨ₀, ?_⟩
  intro V hV hsmall
  obtain ⟨Ψ, hΨ⟩ := hex V hV hsmall
  have hb := field_bounds_of_cNorm_sub_le_one hU hRU hV hV₀ hsmall
  have hVat (x) (hx : x ∈ closedBall x₀ R) : ContDiffAt ℝ 2 V x :=
    (hV.contDiffAt (hU.mem_nhds (hRU hx))).of_le (by simp)
  have hclose (x) (hx : x ∈ closedBall x₀ R) :
      ‖V x - V₀ x‖ ≤ cNorm (closedBall x₀ R) 2 (V - V₀) ∧
      ‖fderiv ℝ V x - fderiv ℝ V₀ x‖ ≤ cNorm (closedBall x₀ R) 2 (V - V₀) := by
    have h := norm_and_fderiv_le_cNorm_two (isCompact_closedBall x₀ R)
      (fun y hy ↦ (hVat y hy).sub (hV₀at y hy)) hx
    rw [fderiv_fun_sub ((hVat x hx).differentiableAt (by norm_num))
      ((hV₀at x hx).differentiableAt (by norm_num))] at h
    exact h
  refine ⟨Ψ, hΨ, hcompare V V₀ Ψ Ψ₀ (cNorm (closedBall x₀ R) 2 (V - V₀))
    hlip₀ hDlip₀ (fun x hx ↦ (hb x hx).2) hDV₀ (cNorm_nonneg _ _ _)
    (fun x hx ↦ (hclose x hx).1) (fun x hx ↦ (hclose x hx).2)
    (hΨ.smooth.of_le (by simp)) (hΨ₀.smooth.of_le (by simp))
    (fun x hx ↦ hΨ.initial x (ball_subset_closedBall hx))
    (fun x hx ↦ hΨ₀.initial x (ball_subset_closedBall hx))
    (fun x hx t ht ↦ hΨ.range x (ball_subset_closedBall hx) t (Ioo_subset_Icc_self ht))
    (fun x hx t ht ↦ hΨ₀.range x (ball_subset_closedBall hx) t (Ioo_subset_Icc_self ht))
    (fun _ hx _ ht ↦ hΨ.hasDerivAt (ball_subset_closedBall hx) ht)
    (fun _ hx _ ht ↦ hΨ₀.hasDerivAt (ball_subset_closedBall hx) ht)
    hΨ.variation_initial hΨ₀.variation_initial hΨ.variation hΨ₀.variation⟩

end JanetCartan.ODE
