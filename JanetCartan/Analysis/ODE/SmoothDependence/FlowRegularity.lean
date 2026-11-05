module

public import JanetCartan.Analysis.ODE.SmoothDependence.FirstDerivative
public import JanetCartan.Analysis.ODE.SmoothDependence.HigherRegularity
public import JanetCartan.Analysis.ODE.SmoothDependence.LinearEvolutionRegularity

/-!
# Higher regularity of local flows

For `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`, bootstrap the actual initial-data derivative
through its linear variational equation. Finite-order induction preserves the
original open domain; passing through all finite orders gives smoothness on
that same domain.
-/

@[expose] public section

open Set
open scoped Topology NNReal

namespace JanetCartan.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`: a continuous uniformly Lipschitz family of
solutions inherits finite joint regularity from its autonomous vector field.
The first derivative is identified by the variational equation, and higher
orders follow from regularity of linear evolution. The time interval is
preserved at every order. -/
theorem contDiffOn_nat_localFlow (n : ℕ)
    {f : E → E} {U s : Set E} {Φ : E × ℝ → E} {a b t₀ : ℝ} {K : ℝ≥0}
    (hU : IsOpen U) (hf : ContDiffOn ℝ n f U) (hs : IsOpen s)
    (ht₀ : t₀ ∈ Ioo a b) (hΦ : ContinuousOn Φ (s ×ˢ Ioo a b))
    (hrange : ∀ x ∈ s, ∀ t ∈ Ioo a b, Φ (x, t) ∈ U)
    (hinit : ∀ x ∈ s, Φ (x, t₀) = x)
    (hode : ∀ x ∈ s, ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ ↦ Φ (x, τ)) (f (Φ (x, t))) t)
    (hlip : ∀ t ∈ Ioo a b, LipschitzOnWith K (fun x ↦ Φ (x, t)) s) :
    ContDiffOn ℝ n Φ (s ×ˢ Ioo a b) := by
  induction n with
  | zero => exact contDiffOn_zero.mpr hΦ
  | succ n ih =>
    have hf' : ContDiffOn ℝ (n + 1) f U := by simpa only [Nat.cast_add, Nat.cast_one] using hf
    have hprev : ContDiffOn ℝ n Φ (s ×ˢ Ioo a b) := ih hf'.of_succ
    obtain ⟨hcd, hJ₀, hJ⟩ := contDiffOn_flow_and_variational_equation
      hU hf'.one_of_succ hs ht₀ hΦ hrange hinit hode hlip
    have hdx (p : E × ℝ) (hp : p ∈ s ×ˢ Ioo a b) :
        HasFDerivAt (fun y ↦ Φ (y, p.2)) (flowInitialDerivative Φ p.1 p.2) p.1 :=
      (((hcd.contDiffAt ((hs.prod isOpen_Ioo).mem_nhds hp)).comp p.1
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)).hasFDerivAt
    have heq (p : E × ℝ) (hp : p ∈ s ×ˢ Ioo a b) :
        flowInitialDerivative Φ p.1 p.2 =
          (fderiv ℝ Φ p).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
      exact ((hcd.differentiableOn (by simp) |>.differentiableAt
        ((hs.prod isOpen_Ioo).mem_nhds hp)).hasFDerivAt.comp p.1
        ((hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1))).fderiv
    have hJcont : ContinuousOn (fun p : E × ℝ ↦ flowInitialDerivative Φ p.1 p.2)
        (s ×ˢ Ioo a b) :=
      ((hcd.continuousOn_fderiv_of_isOpen (hs.prod isOpen_Ioo) le_rfl).clm_comp
        (continuousOn_const (c := ContinuousLinearMap.inl ℝ E ℝ))).congr heq
    have hA : ContDiffOn ℝ n (fun p ↦ fderiv ℝ f (Φ p)) (s ×ˢ Ioo a b) :=
      (hf'.fderiv_of_isOpen hU le_rfl).comp hprev
        (fun p hp ↦ hrange p.1 hp.1 p.2 hp.2)
    have hJs := LinearEvolutionRegularity.contDiffOn_linearEvolution n hs ht₀ hA
      hJcont hJ₀ hJ
    simpa only [Nat.cast_add, Nat.cast_one] using
      contDiffOn_succ_of_contDiffOn_partials hs isOpen_Ioo hJs
        (hf'.of_succ.comp hprev (fun p hp ↦ hrange p.1 hp.1 p.2 hp.2)) hdx
        (fun p hp ↦ hode p.1 hp.1 p.2 hp.2)

/-- `app:lem:common-hamilton-phase`: joint regularity of an autonomous local
flow at any finite order or at order `∞`, on its entire given open domain.
In particular a smooth field gives a smooth flow on one common domain for all
orders. No derivative of the flow in initial data is assumed. -/
theorem contDiffOn_localFlow (n : ℕ∞)
    {f : E → E} {U s : Set E} {Φ : E × ℝ → E} {a b t₀ : ℝ} {K : ℝ≥0}
    (hU : IsOpen U) (hf : ContDiffOn ℝ n f U) (hs : IsOpen s)
    (ht₀ : t₀ ∈ Ioo a b) (hΦ : ContinuousOn Φ (s ×ˢ Ioo a b))
    (hrange : ∀ x ∈ s, ∀ t ∈ Ioo a b, Φ (x, t) ∈ U)
    (hinit : ∀ x ∈ s, Φ (x, t₀) = x)
    (hode : ∀ x ∈ s, ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ ↦ Φ (x, τ)) (f (Φ (x, t))) t)
    (hlip : ∀ t ∈ Ioo a b, LipschitzOnWith K (fun x ↦ Φ (x, t)) s) :
    ContDiffOn ℝ n Φ (s ×ˢ Ioo a b) := by
  apply contDiffOn_iff_forall_nat_le.mpr
  intro m hm
  exact contDiffOn_nat_localFlow m hU (contDiffOn_iff_forall_nat_le.mp hf m hm)
    hs ht₀ hΦ hrange hinit hode hlip

end JanetCartan.ODE
