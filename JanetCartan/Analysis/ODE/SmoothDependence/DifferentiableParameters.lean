module

public import JanetCartan.Analysis.ODE.SmoothDependence.Parameters
public import JanetCartan.Analysis.ODE.SmoothDependence.FirstDerivative

/-!
# Differentiable dependence on constant parameters

For `app:lem:common-hamilton-phase`, lift the vector field to include parameters
with zero velocity. Projection of the lifted variational equation identifies the
actual derivative jointly in the parameter and initial state. In particular this
includes the parameter forcing term, not only the homogeneous state variation.
-/

@[expose] public section

open Set Metric Filter
open scoped NNReal Topology

namespace JanetCartan.ODE

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `app:lem:common-hamilton-phase`: the derivative of a parameterized flow in
its parameter and initial state, with time fixed. -/
noncomputable def parameterizedFlowDerivative (Φ : (P × E) × ℝ → E)
    (z : P × E) (t : ℝ) : (P × E) →L[ℝ] E :=
  fderiv ℝ (fun w ↦ Φ (w, t)) z

/-- `app:lem:common-hamilton-phase`: a continuous uniformly Lipschitz family of
solutions of a `C¹` parameterized vector field is jointly `C¹`. Its actual
derivative `H` in `(p,x)` starts at the state projection and solves
`H' = DV(p,Φ) ∘ (fst,H)` on the full given time interval. Thus a variation
`(δp,δx)` has forcing `DₚV δp` in addition to `DₓV (H (δp,δx))`. -/
theorem contDiffOn_parameterizedFlow_and_variational_equation
    {V : P × E → E} {U s : Set (P × E)} {Φ : (P × E) × ℝ → E}
    {a b t₀ : ℝ} {K : ℝ≥0}
    (hU : IsOpen U) (hV : ContDiffOn ℝ 1 V U) (hs : IsOpen s)
    (ht₀ : t₀ ∈ Ioo a b) (hΦ : ContinuousOn Φ (s ×ˢ Ioo a b))
    (hrange : ∀ z ∈ s, ∀ t ∈ Ioo a b, (z.1, Φ (z, t)) ∈ U)
    (hinit : ∀ z ∈ s, Φ (z, t₀) = z.2)
    (hode : ∀ z ∈ s, ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ ↦ Φ (z, τ)) (V (z.1, Φ (z, t))) t)
    (hlip : ∀ t ∈ Ioo a b, LipschitzOnWith K (fun z ↦ Φ (z, t)) s) :
    ContDiffOn ℝ 1 Φ (s ×ˢ Ioo a b) ∧
      (∀ z ∈ s, parameterizedFlowDerivative Φ z t₀ = ContinuousLinearMap.snd ℝ P E) ∧
      ∀ z ∈ s, ∀ t ∈ Ioo a b,
        HasDerivAt (parameterizedFlowDerivative Φ z)
          ((fderiv ℝ V (z.1, Φ (z, t))).comp
            ((ContinuousLinearMap.fst ℝ P E).prod (parameterizedFlowDerivative Φ z t))) t := by
  let F : P × E → P × E := fun z ↦ (0, V z)
  let Ψ : (P × E) × ℝ → P × E := fun w ↦ (w.1.1, Φ w)
  have hF : ContDiffOn ℝ 1 F U := contDiffOn_const.prodMk hV
  have hΨ : ContinuousOn Ψ (s ×ˢ Ioo a b) :=
    continuous_fst.fst.continuousOn.prodMk hΦ
  have hi : ∀ z ∈ s, Ψ (z, t₀) = z := fun z hz ↦ Prod.ext rfl (hinit z hz)
  have hd : ∀ z ∈ s, ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ ↦ Ψ (z, τ)) (F (Ψ (z, t))) t :=
    fun z hz t ht ↦ (hasDerivAt_const t z.1).prodMk (hode z hz t ht)
  have hl : ∀ t ∈ Ioo a b,
      LipschitzOnWith (max 1 K) (fun z ↦ Ψ (z, t)) s :=
    fun t ht ↦ LipschitzWith.prod_fst.lipschitzOnWith.prodMk (hlip t ht)
  obtain ⟨hcd, hJ₀, hJ⟩ := contDiffOn_flow_and_variational_equation hU hF hs ht₀
    hΨ hrange hi hd hl
  have hslice (z) (hz : z ∈ s) (t) (ht : t ∈ Ioo a b) :
      DifferentiableAt ℝ (fun w ↦ Φ (w, t)) z :=
    ((hcd.snd.contDiffAt ((hs.prod isOpen_Ioo).mem_nhds ⟨hz, ht⟩)).comp z
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have heq (z) (hz : z ∈ s) (t) (ht : t ∈ Ioo a b) :
      flowInitialDerivative Ψ z t =
        (ContinuousLinearMap.fst ℝ P E).prod (parameterizedFlowDerivative Φ z t) :=
    ((ContinuousLinearMap.fst ℝ P E).hasFDerivAt.prodMk (hslice z hz t ht).hasFDerivAt).fderiv
  have hproj (z) (hz : z ∈ s) (t) (ht : t ∈ Ioo a b) :
      (ContinuousLinearMap.snd ℝ P E).comp (flowInitialDerivative Ψ z t) =
        parameterizedFlowDerivative Φ z t := by
    rw [heq z hz t ht]
    exact ContinuousLinearMap.ext (fun w ↦ rfl)
  refine ⟨hcd.snd, ?_, ?_⟩
  · intro z hz
    rw [← hproj z hz t₀ ht₀, hJ₀ z hz]
    exact ContinuousLinearMap.comp_id _
  · intro z hz t ht
    have hDF : fderiv ℝ F (Ψ (z, t)) =
        (0 : (P × E) →L[ℝ] P).prod (fderiv ℝ V (Ψ (z, t))) :=
      ((hasFDerivAt_const (0 : P) (Ψ (z, t))).prodMk
        (hV.differentiableOn (by simp) |>.differentiableAt
          (hU.mem_nhds (hrange z hz t ht))).hasFDerivAt).fderiv
    have hp := ((ContinuousLinearMap.compL ℝ (P × E) (P × E) E)
      (ContinuousLinearMap.snd ℝ P E)).hasFDerivAt.comp_hasDerivAt t (hJ z hz t ht)
    change HasDerivAt (fun τ ↦ (ContinuousLinearMap.snd ℝ P E).comp
      (flowInitialDerivative Ψ z τ))
      ((ContinuousLinearMap.snd ℝ P E).comp
        ((fderiv ℝ F (Ψ (z, t))).comp (flowInitialDerivative Ψ z t))) t at hp
    rw [hDF, heq z hz t ht] at hp
    apply hp.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    exact (hproj z hz τ hτ).symm

/-- `app:lem:common-hamilton-phase`: parameters and initial states share a
bounded open local flow domain with joint `C¹` regularity and the full
parameter variational equation. The closed domain retains the range buffer,
continuity, and a uniform Lipschitz bound. -/
theorem exists_contDiffOn_one_parameterized_localFlow_in_open
    {V : P × E → E} {z₀ : P × E} {U : Set (P × E)}
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hV : ContDiffOn ℝ 1 V U) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : (P × E) × ℝ → E,
      ContDiffOn ℝ 1 Φ (ball z₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
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
  obtain ⟨r, hr, ε, hε, Φ, hc, hi, hd, hmem, K, hK⟩ :=
    exists_parameterized_localFlow_in_open hU hz₀ (hV.contDiffAt (hU.mem_nhds hz₀)) t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  obtain ⟨hcd, hJ₀, hJ⟩ := contDiffOn_parameterizedFlow_and_variational_equation
    hU hV isOpen_ball ht₀ (hc.mono (prod_mono ball_subset_closedBall Ioo_subset_Icc_self))
    (fun z hz t ht ↦ hmem z (ball_subset_closedBall hz) t (Ioo_subset_Icc_self ht))
    (fun z hz ↦ hi z (ball_subset_closedBall hz))
    (fun z hz t ht ↦ hd z (ball_subset_closedBall hz) t ht)
    (fun t ht ↦ (hK t (Ioo_subset_Icc_self ht)).mono ball_subset_closedBall)
  exact ⟨r, hr, ε, hε, Φ, hcd, hc, hi, hd, hmem, hJ₀, hJ, K, hK⟩

end JanetCartan.ODE
