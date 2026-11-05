module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.RadialCharts

/-!
# Covariance of the original homogeneous root Hamilton field

Differentiate degree-one homogeneity on the original open conic domain.
These identities supply the ODE and variational equation for the literal
radial flow in `FlowTransport`, without changing the scalar root or time.
Source: `app:ch_regular:lem:finite-chain` and
`app:ch_regular:eq:joint-stationary`.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior

open RegularSector.Characteristic

variable {d : ℕ}

/-- Differentiate the original root's degree-one homogeneity on its open
radially invariant domain. Consumer: the Hamilton-field covariance needed by
`isSmoothFlowOn_radialFlow` (`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_root_comp_rootRadialEquiv
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hroot : ∀ w ∈ D, ∀ a : ℝ, 0 < a →
      (w.1, (w.2.1, a • w.2.2)) ∈ D ∧ h (w.1, (w.2.1, a • w.2.2)) = a * h w)
    {a : ℝ} (ha : 0 < a) {w : RootState (Euclidean d)} (hw : w ∈ D) :
    (fderiv ℝ h (rootRadialEquiv a ha.ne' w)).comp
      (rootRadialEquiv a ha.ne').toContinuousLinearMap = a • fderiv ℝ h w := by
  have hd (v) (hv : v ∈ D) : DifferentiableAt ℝ h v :=
    (hh.contDiffAt (hD.mem_nhds hv)).differentiableAt (by simp)
  have hleft := (hd _ (hroot w hw a ha).1).hasFDerivAt.comp w
    (rootRadialEquiv a ha.ne').hasFDerivAt
  have hright := (hd w hw).hasFDerivAt.const_smul a
  have he : (fun v ↦ h (rootRadialEquiv a ha.ne' v)) =ᶠ[𝓝 w] (fun v ↦ a • h v) := by
    filter_upwards [hD.mem_nhds hw] with v hv using (hroot v hv a ha).2
  exact hleft.unique (hright.congr_of_eventuallyEq he)

/-- The position gradient has degree one and the momentum gradient degree
zero, derived from the actual root differential. Consumer: the same-field ODE
under radial transport (`app:ch_regular:lem:finite-chain`). -/
theorem rootGradients_rootRadialEquiv
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hroot : ∀ w ∈ D, ∀ a : ℝ, 0 < a →
      (w.1, (w.2.1, a • w.2.2)) ∈ D ∧ h (w.1, (w.2.1, a • w.2.2)) = a * h w)
    {a : ℝ} (ha : 0 < a) {w : RootState (Euclidean d)} (hw : w ∈ D) :
    rootPositionGradient h (rootRadialEquiv a ha.ne' w) = a • rootPositionGradient h w ∧
    rootMomentumGradient h (rootRadialEquiv a ha.ne' w) = rootMomentumGradient h w := by
  have he := fderiv_root_comp_rootRadialEquiv hD hh hroot ha hw
  have hy : (fderiv ℝ h (rootRadialEquiv a ha.ne' w)).comp
      ((ContinuousLinearMap.inr ℝ ℝ (Euclidean d × Euclidean d)).comp
        (ContinuousLinearMap.inl ℝ (Euclidean d) (Euclidean d))) =
      a • (fderiv ℝ h w).comp
      ((ContinuousLinearMap.inr ℝ ℝ (Euclidean d × Euclidean d)).comp
        (ContinuousLinearMap.inl ℝ (Euclidean d) (Euclidean d))) := by
    ext v
    simpa using DFunLike.congr_fun he (0, (v, 0))
  have hp : (fderiv ℝ h (rootRadialEquiv a ha.ne' w)).comp
      ((ContinuousLinearMap.inr ℝ ℝ (Euclidean d × Euclidean d)).comp
        (ContinuousLinearMap.inr ℝ (Euclidean d) (Euclidean d))) =
      (fderiv ℝ h w).comp
      ((ContinuousLinearMap.inr ℝ ℝ (Euclidean d × Euclidean d)).comp
        (ContinuousLinearMap.inr ℝ (Euclidean d) (Euclidean d))) := by
    ext v
    have hv := DFunLike.congr_fun he (0, (0, v))
    have heq : (0, (0, a • v)) = a • ((0, (0, v)) : RootState (Euclidean d)) := by simp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      rootRadialEquiv_apply, smul_apply, smul_eq_mul] at hv
    rw [heq, map_smul, smul_eq_mul] at hv
    exact mul_left_cancel₀ ha.ne' hv
  constructor
  · simp only [rootPositionGradient, hy, map_smul]
  · simp only [rootMomentumGradient, hp]

/-- Positive radial conjugacy preserves the SAME root Hamilton field,
including its unit time component. No covariance identity is assumed.
Consumer: radial copies in `app:ch_regular:eq:joint-stationary`. -/
theorem rootHamiltonField_rootRadialEquiv
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hroot : ∀ w ∈ D, ∀ a : ℝ, 0 < a →
      (w.1, (w.2.1, a • w.2.2)) ∈ D ∧ h (w.1, (w.2.1, a • w.2.2)) = a * h w)
    {a : ℝ} (ha : 0 < a) {w : RootState (Euclidean d)} (hw : w ∈ D) :
    rootHamiltonField h (rootRadialEquiv a ha.ne' w) =
      rootRadialEquiv a ha.ne' (rootHamiltonField h w) := by
  obtain ⟨hy, hp⟩ := rootGradients_rootRadialEquiv hD hh hroot ha hw
  rw [rootHamiltonField, hp, hy]
  rfl

/-- Differentiate the proved Hamilton-field covariance. Consumer: the actual
variational equation of the transported flow in `isSmoothFlowOn_radialFlow`
(`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_rootHamiltonField_comp_rootRadialEquiv
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hroot : ∀ w ∈ D, ∀ a : ℝ, 0 < a →
      (w.1, (w.2.1, a • w.2.2)) ∈ D ∧ h (w.1, (w.2.1, a • w.2.2)) = a * h w)
    {a : ℝ} (ha : 0 < a) {w : RootState (Euclidean d)} (hw : w ∈ D) :
    (fderiv ℝ (rootHamiltonField h) (rootRadialEquiv a ha.ne' w)).comp
      (rootRadialEquiv a ha.ne').toContinuousLinearMap =
    (rootRadialEquiv a ha.ne').toContinuousLinearMap.comp
      (fderiv ℝ (rootHamiltonField h) w) := by
  have hd (v) (hv : v ∈ D) : DifferentiableAt ℝ (rootHamiltonField h) v :=
    ((contDiffOn_rootHamiltonField hD hh).contDiffAt
      (hD.mem_nhds hv)).differentiableAt (by simp)
  have hleft := (hd _ (hroot w hw a ha).1).hasFDerivAt.comp w
    (rootRadialEquiv a ha.ne').hasFDerivAt
  have hright := (rootRadialEquiv a ha.ne').hasFDerivAt.comp w (hd w hw).hasFDerivAt
  apply hleft.unique
  apply hright.congr_of_eventuallyEq
  filter_upwards [hD.mem_nhds hw] with v hv using rootHamiltonField_rootRadialEquiv hD hh hroot ha hv


end JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior
