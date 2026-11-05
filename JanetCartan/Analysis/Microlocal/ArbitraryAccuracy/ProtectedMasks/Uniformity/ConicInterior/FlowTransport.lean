module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.FlowTransport.Covariance
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RootFamily.Field
public import JanetCartan.Analysis.ODE.FlowStability

/-!
# Smooth radial transport of the same root flow

Conjugate the original flow by `rootRadialEquiv`, retaining the entire elapsed
interval and deriving both the ODE and the actual variational equation from
root homogeneity. The larger range ball is only a containing ball: the proof
uses the original trajectories and their radial images to control the domain.

Consumer: the radial expansion of the finite family used by
`exists_uniform_nested_physicalDirectLocalizers`, for
`app:ch_regular:lem:finite-chain` and `app:ch_regular:thm:no-return`.
Final finite-family selection and mask instantiation remain with that consumer.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior

open RegularSector.Characteristic

variable {d : ℕ}

/-- The actual initial-data derivative transforms by conjugation. This is an
identity for `fderiv`, even where the original map is not differentiable;
it does not introduce a candidate derivative. Consumer: the transported
variational equation (`app:ch_regular:lem:finite-chain`). -/
theorem flowInitialDerivative_radialFlow (a : ℝ) (ha : a ≠ 0)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (w : RootState (Euclidean d)) (t : ℝ) :
    ODE.flowInitialDerivative (radialFlow a ha Φ) w t =
      (rootRadialEquiv a ha).toContinuousLinearMap.comp
        ((ODE.flowInitialDerivative Φ ((rootRadialEquiv a ha).symm w) t).comp
          (rootRadialEquiv a ha).symm.toContinuousLinearMap) := by
  change fderiv ℝ ((rootRadialEquiv a ha) ∘
    ((fun v ↦ Φ (v, t)) ∘ (rootRadialEquiv a ha).symm)) w = _
  rw [ContinuousLinearEquiv.comp_fderiv, ContinuousLinearEquiv.comp_right_fderiv]
  rfl

/-- Radial conjugation gives a smooth flow of the SAME homogeneous root on
the original elapsed interval `T`. Every field of `ODE.IsSmoothFlowOn`,
including its actual initial-data derivative and variational equation, is proved.

The hypotheses `hh` and the homogeneity part of `hroot` are produced by
`UniformGeometry.exists_uniform_fieldRoot_conicGeometry`; its domain part is
`RootFamily.fieldDomain_smul`. The original range control supplies `hRD`,
and radial buffer refinement supplies the three geometric inclusions. Only
actual trajectories must lie in `D`; the containing ball `closedBall z' R'`
need not lie there. Consumer: the expanded-family application of
`exists_uniform_nested_physicalDirectLocalizers` for
`app:ch_regular:lem:finite-chain` and `app:ch_regular:thm:no-return`. -/
theorem isSmoothFlowOn_radialFlow
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hroot : ∀ w ∈ D, ∀ a : ℝ, 0 < a →
      (w.1, (w.2.1, a • w.2.2)) ∈ D ∧ h (w.1, (w.2.1, a • w.2.2)) = a * h w)
    {a : ℝ} (ha : 0 < a)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {z z' : RootState (Euclidean d)} {R r R' r' T : ℝ}
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z R r T Φ)
    (hRD : closedBall z R ⊆ D)
    (hclosed : (rootRadialEquiv a ha.ne').symm '' closedBall z' r' ⊆ closedBall z r)
    (hopen : (rootRadialEquiv a ha.ne').symm '' ball z' r' ⊆ ball z r)
    (hrange : rootRadialEquiv a ha.ne' '' closedBall z R ⊆ closedBall z' R') :
    ODE.IsSmoothFlowOn (rootHamiltonField h) z' R' r' T (radialFlow a ha.ne' Φ) := by
  let S := rootRadialEquiv (d := d) a ha.ne'
  have hc (w) (hw : w ∈ closedBall z' r') : S.symm w ∈ closedBall z r :=
    hclosed ⟨w, hw, rfl⟩
  have ho (w) (hw : w ∈ ball z' r') : S.symm w ∈ ball z r :=
    hopen ⟨w, hw, rfl⟩
  have hinit (w) (hw : w ∈ closedBall z' r') : radialFlow a ha.ne' Φ (w, 0) = w := by
    change S (Φ (S.symm w, 0)) = w
    rw [hΦ.initial _ (hc w hw), S.apply_symm_apply]
  refine ⟨hinit, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw t ht
    have hd := S.hasFDerivAt.comp_hasDerivWithinAt t (hΦ.ode _ (hc w hw) t ht)
    have hcov := rootHamiltonField_rootRadialEquiv hD hh hroot ha (hRD (hΦ.range _ (hc w hw) t ht))
    change HasDerivWithinAt (fun s ↦ S (Φ (S.symm w, s)))
      (rootHamiltonField h (S (Φ (S.symm w, t)))) (Icc (-T) T) t
    rw [hcov]
    exact hd
  · intro w hw t ht
    exact hrange ⟨_, hΦ.range _ (hc w hw) t ht, rfl⟩
  · exact S.continuous.comp_continuousOn
      (hΦ.continuous.comp
        ((S.symm.continuous.comp continuous_fst).prodMk continuous_snd).continuousOn
        (fun p hp ↦ ⟨hc p.1 hp.1, hp.2⟩))
  · exact S.contDiff.comp_contDiffOn
      (hΦ.smooth.comp
        ((S.symm.contDiff.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
        (fun p hp ↦ ⟨ho p.1 hp.1, hp.2⟩))
  · intro w hw
    exact ODE.flowInitialDerivative_initialTime isOpen_ball hw
      (fun v hv ↦ hinit v (ball_subset_closedBall hv))
  · intro w hw t ht
    have hJ := (hasDerivAt_const t S.toContinuousLinearMap).clm_comp
      ((hΦ.variation _ (ho w hw) t ht).clm_comp
        (hasDerivAt_const t S.symm.toContinuousLinearMap))
    simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero,
      zero_add, add_zero] at hJ
    have hcov := fderiv_rootHamiltonField_comp_rootRadialEquiv hD hh hroot ha
      (hRD (hΦ.range _ (ball_subset_closedBall (ho w hw)) t (Ioo_subset_Icc_self ht)))
    have hJ' := hJ.congr_of_eventuallyEq (Eventually.of_forall
      (fun s ↦ flowInitialDerivative_radialFlow a ha.ne' Φ w s))
    convert hJ' using 1
    rw [flowInitialDerivative_radialFlow]
    change (fderiv ℝ (rootHamiltonField h) (S (Φ (S.symm w, t)))).comp
        (S.toContinuousLinearMap.comp
          ((ODE.flowInitialDerivative Φ (S.symm w) t).comp S.symm.toContinuousLinearMap)) = _
    rw [← ContinuousLinearMap.comp_assoc, hcov]
    simp only [S, ContinuousLinearMap.comp_assoc]

/-- Actual transported trajectories stay in the original radial domain.
There is no domain-containment assumption on the new enclosing ball.
`RootFamily.fieldDomain_smul` supplies `hrad` for the original field domain.
Consumer: whole protected segments in `app:ch_regular:thm:no-return`. -/
theorem radialFlow_mem_domain
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    {a : ℝ} (ha : 0 < a)
    (hrad : MapsTo (rootRadialEquiv a ha.ne') D D)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {z z' : RootState (Euclidean d)} {R r r' T : ℝ}
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z R r T Φ)
    (hRD : closedBall z R ⊆ D)
    (hclosed : (rootRadialEquiv a ha.ne').symm '' closedBall z' r' ⊆ closedBall z r)
    {w : RootState (Euclidean d)} (hw : w ∈ closedBall z' r')
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    radialFlow a ha.ne' Φ (w, t) ∈ D :=
  hrad (hRD (hΦ.range _ (hclosed ⟨w, hw, rfl⟩) t ht))

/-- Apply radial flow transport to the original coefficient root and domain.
The scalar smoothness and homogeneity inputs are exactly the outputs of
`UniformGeometry.exists_uniform_fieldRoot_conicGeometry` (and `RootFlow`).
Radial invariance is discharged by `fieldDomain_smul`, and openness by
`isOpen_fieldDomain`; no root, coefficient field, or elapsed time is changed.
The three remaining geometric inclusions are the radial buffer refinement's
outputs. Consumer: the parent's expanded-family application of
`exists_uniform_nested_physicalDirectLocalizers`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:thm:no-return`). -/
theorem isSmoothFlowOn_radialFlow_fieldRoot
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean (d + 1))} (hΩ : IsOpen Ω)
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d) (ε : ℝ)
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (H : (Fin (d + 1) → MetricTensor (d + 1)) × Euclidean d → ℝ)
    (hh : ContDiffOn ℝ ∞ (RootFamily.fieldRoot e Q H)
      (RootFamily.fieldDomain e Ω ℓ η₀ ε))
    (hhom : ∀ w ∈ RootFamily.fieldDomain e Ω ℓ η₀ ε, ∀ a : ℝ, 0 < a →
      RootFamily.fieldRoot e Q H (w.1, (w.2.1, a • w.2.2)) =
        a * RootFamily.fieldRoot e Q H w)
    {a : ℝ} (ha : 0 < a)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {z z' : RootState (Euclidean d)} {R r R' r' T : ℝ}
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField (RootFamily.fieldRoot e Q H)) z R r T Φ)
    (hRD : closedBall z R ⊆ RootFamily.fieldDomain e Ω ℓ η₀ ε)
    (hclosed : (rootRadialEquiv a ha.ne').symm '' closedBall z' r' ⊆ closedBall z r)
    (hopen : (rootRadialEquiv a ha.ne').symm '' ball z' r' ⊆ ball z r)
    (hrange : rootRadialEquiv a ha.ne' '' closedBall z R ⊆ closedBall z' R') :
    ODE.IsSmoothFlowOn (rootHamiltonField (RootFamily.fieldRoot e Q H))
      z' R' r' T (radialFlow a ha.ne' Φ) :=
  isSmoothFlowOn_radialFlow (RootFamily.isOpen_fieldDomain e hΩ ℓ η₀ ε) hh
    (fun w hw b hb ↦ ⟨RootFamily.fieldDomain_smul e Ω ℓ η₀ ε hw hb, hhom w hw b hb⟩)
    ha hΦ hRD hclosed hopen hrange

end JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior
