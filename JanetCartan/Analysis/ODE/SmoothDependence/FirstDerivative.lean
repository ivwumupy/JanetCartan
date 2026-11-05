module

public import JanetCartan.Analysis.ODE.SmoothDependence.FirstDerivative.UniformRemainder
public import JanetCartan.Analysis.ODE.SmoothDependence.FirstDerivative.VariationError
public import JanetCartan.Analysis.ODE.SmoothDependence.FirstDerivative.JointRegularity
public import JanetCartan.Analysis.ODE.SmoothDependence.FirstDerivative.LinearEvolution

/-!
# Identifying a flow's first derivative

For `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`, the nonlinear flow derivative is identified
with a candidate variational solution by estimating the Taylor remainder.
This argument does not assume any initial-data differentiability of the flow.

The final theorem constructs the jointly continuous variational solution from
the continuous coefficient `Df ∘ Φ`, then identifies it with the actual
initial-data derivative. Thus joint `C¹` regularity and the variational equation
hold on the entire original open time interval.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal

namespace JanetCartan.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:ch_regular_base:lem:buffered-interpolation`: the initial-data derivative
of a flow. Its identification with a variational solution is proved below. -/
noncomputable def flowInitialDerivative (Φ : E × ℝ → E) (x : E) (t : ℝ) : E →L[ℝ] E :=
  fderiv ℝ (fun y ↦ Φ (y, t)) x

/-- `app:lem:common-hamilton-phase`: at the initial time, the flow's
initial-data derivative is the identity on every open initial-data domain. -/
theorem flowInitialDerivative_initialTime {Φ : E × ℝ → E} {s : Set E} {x : E} {t₀ : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (hinit : ∀ y ∈ s, Φ (y, t₀) = y) :
    flowInitialDerivative Φ x t₀ = ContinuousLinearMap.id ℝ E := by
  apply HasFDerivAt.fderiv
  apply (hasFDerivAt_id x).congr_of_eventuallyEq
  filter_upwards [hs.mem_nhds hx] with y hy using hinit y hy

/-- `app:ch_regular_base:lem:buffered-interpolation`: a solution of the
linearized IVP is the actual initial-data derivative of the nonlinear flow.
The proof uses a uniform Taylor remainder and Grönwall, not an interchange of
derivatives. The closed time segment may run in either direction. -/
theorem hasFDerivAt_flow_of_variational_solution
    {f : E → E} {U s : Set E} {Φ : E × ℝ → E} {x : E} {t₀ t : ℝ} {K : ℝ≥0}
    {J : ℝ → E →L[ℝ] E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hs : IsOpen s) (hx : x ∈ s)
    (hΦ : ContinuousOn (fun τ ↦ Φ (x, τ)) (uIcc t₀ t))
    (hrange : ∀ τ ∈ uIcc t₀ t, Φ (x, τ) ∈ U)
    (hinit : ∀ y ∈ s, Φ (y, t₀) = y)
    (hode : ∀ y ∈ s, ∀ τ ∈ uIcc t₀ t,
      HasDerivAt (fun σ ↦ Φ (y, σ)) (f (Φ (y, τ))) τ)
    (hlip : ∀ τ ∈ uIcc t₀ t, LipschitzOnWith K (fun y ↦ Φ (y, τ)) s)
    (hJinit : J t₀ = ContinuousLinearMap.id ℝ E)
    (hJ : ∀ τ ∈ uIcc t₀ t,
      HasDerivAt J ((fderiv ℝ f (Φ (x, τ))).comp (J τ)) τ) :
    HasFDerivAt (fun y ↦ Φ (y, t)) (J t) x := by
  have hA : ContinuousOn (fun τ ↦ fderiv ℝ f (Φ (x, τ))) (uIcc t₀ t) :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).comp hΦ hrange
  obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn hA
  let L := max M 1
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hAL (τ) (hτ : τ ∈ uIcc t₀ t) : ‖fderiv ℝ f (Φ (x, τ))‖ ≤ L :=
    (hM τ hτ).trans (le_max_left _ _)
  let C := (Real.exp (L * |t - t₀|) - 1) / L
  have hC : 0 ≤ C := div_nonneg
    (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hL.le (abs_nonneg _)))) hL.le
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  let ε := c / (C + 1)
  have hε : 0 < ε := div_pos hc (by positivity)
  have hεC : ε * C ≤ c := by
    calc
      ε * C ≤ ε * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = c := div_mul_cancel₀ c (by positivity)
  filter_upwards [hs.mem_nhds hx,
    eventually_uniform_flow_remainder hU hf (hs.mem_nhds hx) isCompact_uIcc
      hΦ hrange hlip hε] with y hy hrem
  have hb := flow_variation_error_le (hu := hode x hx) (hv := hode y hy) hJ
    (h := y - x) (by simp [hinit y hy, hinit x hx, hJinit]) hAL hrem
  calc
    ‖Φ (y, t) - Φ (x, t) - J t (y - x)‖
        ≤ gronwallBound 0 L (ε * ‖y - x‖) |t - t₀| := hb
    _ = (ε * C) * ‖y - x‖ := by
      rw [gronwallBound_of_K_ne_0 hL.ne']
      dsimp [C]
      ring
    _ ≤ c * ‖y - x‖ := mul_le_mul_of_nonneg_right hεC (norm_nonneg _)

/-- `app:lem:common-hamilton-phase`: once a jointly continuous solution of the
linearized IVP has been constructed, the flow is jointly `C¹` and its actual
initial-data derivative satisfies the variational equation throughout the
original open time interval. The extra variational-solution input must be
constructed separately before applying this result to a nonlinear flow. -/
theorem contDiffOn_flow_of_continuous_variational_solution
    {f : E → E} {U s : Set E} {Φ : E × ℝ → E} {a b t₀ : ℝ} {K : ℝ≥0}
    {J : E × ℝ → E →L[ℝ] E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hs : IsOpen s)
    (ht₀ : t₀ ∈ Ioo a b) (hΦ : ContinuousOn Φ (s ×ˢ Ioo a b))
    (hrange : ∀ x ∈ s, ∀ t ∈ Ioo a b, Φ (x, t) ∈ U)
    (hinit : ∀ x ∈ s, Φ (x, t₀) = x)
    (hode : ∀ x ∈ s, ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ ↦ Φ (x, τ)) (f (Φ (x, t))) t)
    (hlip : ∀ t ∈ Ioo a b, LipschitzOnWith K (fun x ↦ Φ (x, t)) s)
    (hJcont : ContinuousOn J (s ×ˢ Ioo a b))
    (hJinit : ∀ x ∈ s, J (x, t₀) = ContinuousLinearMap.id ℝ E)
    (hJ : ∀ x ∈ s, ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ ↦ J (x, τ))
        ((fderiv ℝ f (Φ (x, t))).comp (J (x, t))) t) :
    ContDiffOn ℝ 1 Φ (s ×ˢ Ioo a b) ∧
      (∀ x ∈ s, flowInitialDerivative Φ x t₀ = ContinuousLinearMap.id ℝ E) ∧
      ∀ x ∈ s, ∀ t ∈ Ioo a b,
        HasDerivAt (flowInitialDerivative Φ x)
          ((fderiv ℝ f (Φ (x, t))).comp (flowInitialDerivative Φ x t)) t := by
  have hdx (x) (hx : x ∈ s) (t) (ht : t ∈ Ioo a b) :
      HasFDerivAt (fun y ↦ Φ (y, t)) (J (x, t)) x := by
    have hsub := ordConnected_Ioo.uIcc_subset ht₀ ht
    apply hasFDerivAt_flow_of_variational_solution hU hf hs hx
      (J := fun τ ↦ J (x, τ))
    · exact hΦ.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun τ hτ ↦ ⟨hx, hsub hτ⟩)
    · exact fun τ hτ ↦ hrange x hx τ (hsub hτ)
    · exact hinit
    · exact fun y hy τ hτ ↦ hode y hy τ (hsub hτ)
    · exact fun τ hτ ↦ hlip τ (hsub hτ)
    · exact hJinit x hx
    · exact fun τ hτ ↦ hJ x hx τ (hsub hτ)
  have heq (x) (hx : x ∈ s) (t) (ht : t ∈ Ioo a b) :
      flowInitialDerivative Φ x t = J (x, t) := (hdx x hx t ht).fderiv
  refine ⟨?_, fun x hx ↦ flowInitialDerivative_initialTime hs hx hinit, ?_⟩
  · exact contDiffOn_one_of_continuous_partials hs isOpen_Ioo hJcont
      (hf.continuousOn.comp hΦ (fun p hp ↦ hrange p.1 hp.1 p.2 hp.2))
      (fun p hp ↦ hdx p.1 hp.1 p.2 hp.2) (fun p hp ↦ hode p.1 hp.1 p.2 hp.2)
  · intro x hx t ht
    rw [heq x hx t ht]
    apply (hJ x hx t ht).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ using heq x hx τ hτ

/-- `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`: a continuous autonomous flow of a `C¹` vector
field, uniformly Lipschitz in its initial data, is jointly `C¹` on its open
domain. Its actual initial-data derivative starts at the identity and solves
the variational equation on the whole original time interval.

The continuous linear evolution is constructed from `Df ∘ Φ`; differentiability
in the initial data is then proved by the uniform Taylor remainder and Grönwall
estimate. No differentiability of the flow in its initial data is assumed. -/
theorem contDiffOn_flow_and_variational_equation [CompleteSpace E]
    {f : E → E} {U s : Set E} {Φ : E × ℝ → E} {a b t₀ : ℝ} {K : ℝ≥0}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hs : IsOpen s)
    (ht₀ : t₀ ∈ Ioo a b) (hΦ : ContinuousOn Φ (s ×ˢ Ioo a b))
    (hrange : ∀ x ∈ s, ∀ t ∈ Ioo a b, Φ (x, t) ∈ U)
    (hinit : ∀ x ∈ s, Φ (x, t₀) = x)
    (hode : ∀ x ∈ s, ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ ↦ Φ (x, τ)) (f (Φ (x, t))) t)
    (hlip : ∀ t ∈ Ioo a b, LipschitzOnWith K (fun x ↦ Φ (x, t)) s) :
    ContDiffOn ℝ 1 Φ (s ×ˢ Ioo a b) ∧
      (∀ x ∈ s, flowInitialDerivative Φ x t₀ = ContinuousLinearMap.id ℝ E) ∧
      ∀ x ∈ s, ∀ t ∈ Ioo a b,
        HasDerivAt (flowInitialDerivative Φ x)
          ((fderiv ℝ f (Φ (x, t))).comp (flowInitialDerivative Φ x t)) t := by
  have hA : ContinuousOn (fun p ↦ fderiv ℝ f (Φ p)) (s ×ˢ Ioo a b) :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).comp hΦ
      (fun p hp ↦ hrange p.1 hp.1 p.2 hp.2)
  obtain ⟨J, hJcont, hJinit, hJ⟩ := exists_continuous_linearEvolution ht₀ hA
  exact contDiffOn_flow_of_continuous_variational_solution hU hf hs ht₀ hΦ
    hrange hinit hode hlip hJcont hJinit hJ

end JanetCartan.ODE
