module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.SliceJacobian
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.ForwardJacobian

/-!
# Refining the retained positive reference before fixing its masks

The source construction supplies a half-gap for the full augmented map. That
bound alone has no perturbation slack. We normalize by the actual differential
at the retained center and shrink the input neighborhood to obtain a quarter-gap.
The literal slice Jacobian is positive and smooth on an open buffer.

Consumer: the fixed-domain inverse construction for
`exists_retained_conic_primitives_sub_tolerance`; sources:
`app:ch_background:eq:bg-Psi`, `app:ch_background:eq:bg-jacobian`, and
`app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormalReduction.TransportSymbol FullPhaseCharts

/-- Refine, and renormalize, the SAME retained transport near its center.
The input half-gap is supplied by the source conic chart, after identifying
its transport with the retained Hamilton transport. No inverse regularity is
assumed. The new normalization is the actual central augmented differential;
the resulting quarter-gap leaves room for a subsequent perturbation.
Consumer: common inverse stability for `bg-Psi` and `bg-jacobian`. -/
theorem exists_retained_augmented_refinement
    {n : ℕ} {Y₀ : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {H : Set (InputVariables n)} {p₀ : InputVariables n}
    (hH : IsOpen H) (hp₀ : p₀ ∈ H)
    (hf : ContDiffOn ℝ ∞ (augmentedTransportGradient Y₀) H)
    (A₀ : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (hgap : ‖A₀.symm.toContinuousLinearMap.comp
      (fderiv ℝ (augmentedTransportGradient Y₀) p₀) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)
    (slice : TransportSliceCoordinates n) :
    ∃ A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2,
      A.toContinuousLinearMap = fderiv ℝ (augmentedTransportGradient Y₀) p₀ ∧
    ∃ ρ > (0 : ℝ), closedBall p₀ (2 * ρ) ⊆ H ∧
    ∃ gap > (0 : ℝ),
      (∀ p ∈ closedBall p₀ (2 * ρ),
        ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient Y₀) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 4) ∧
      (∀ p ∈ closedBall p₀ (2 * ρ),
        gap ≤ transportAbsoluteJacobian slice Y₀ p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian slice Y₀) (ball p₀ (2 * ρ)) := by
  let L := fderiv ℝ (augmentedTransportGradient Y₀) p₀
  have hb : Function.Bijective (A₀.symm.toContinuousLinearMap.comp L) :=
    bijective_of_normalized_gap (ContinuousLinearEquiv.refl ℝ _) (by simpa using hgap)
  have hL : Function.Bijective L :=
    ⟨fun x y hxy ↦ hb.1 (congrArg A₀.symm hxy), fun y ↦ by
      obtain ⟨x, hx⟩ := hb.2 (A₀.symm y)
      exact ⟨x, A₀.symm.injective hx⟩⟩
  let A := (LinearEquiv.ofBijective L.toLinearMap hL).toContinuousLinearEquiv
  have hA : A.toContinuousLinearMap = L := rfl
  have hdf : ContDiffOn ℝ ∞ (fderiv ℝ (augmentedTransportGradient Y₀)) H :=
    hf.fderiv_of_isOpen hH (by simp)
  have hc : ContinuousAt (fun p ↦ ‖A.symm.toContinuousLinearMap.comp
      (fderiv ℝ (augmentedTransportGradient Y₀) p) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖) p₀ :=
    ((continuousAt_const.clm_comp (hdf.continuousOn.continuousAt (hH.mem_nhds hp₀))).sub
      continuousAt_const).norm
  have hzero : A.symm.toContinuousLinearMap.comp L =
      ContinuousLinearMap.id ℝ (InputVariables n) := by
    rw [← hA]
    apply ContinuousLinearMap.ext
    intro x
    exact A.symm_apply_apply x
  have hnear : ∀ᶠ p in 𝓝 p₀, ‖A.symm.toContinuousLinearMap.comp
      (fderiv ℝ (augmentedTransportGradient Y₀) p) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ < 1 / 4 :=
    hc.eventually (gt_mem_nhds (by
      change ‖A.symm.toContinuousLinearMap.comp L - _‖ < _
      rw [hzero, sub_self, norm_zero]
      norm_num))
  have hpos : 0 < transportAbsoluteJacobian slice Y₀ p₀ :=
    transportAbsoluteJacobian_pos_of_augmented_injective slice
      ((hf.contDiffAt (hH.mem_nhds hp₀)).differentiableAt (by simp)) hL.1
  have hslice := transportSliceDifferential_contDiffOn slice Y₀ hH hf.fst.snd.snd
  have hdet := NormalComparison.contDiff_normalJacobianDet.comp_contDiffOn hslice
  have hj : ContinuousAt (transportAbsoluteJacobian slice Y₀) p₀ :=
    (hdet.continuousOn.continuousAt (hH.mem_nhds hp₀)).abs
  have hjnear : ∀ᶠ p in 𝓝 p₀,
      transportAbsoluteJacobian slice Y₀ p₀ / 2 < transportAbsoluteJacobian slice Y₀ p :=
    hj.eventually (lt_mem_nhds (half_lt_self hpos))
  obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hH.eventually_mem hp₀).and (hnear.and hjnear))
  have hsub : closedBall p₀ (2 * (d / 4)) ⊆ ball p₀ d :=
    closedBall_subset_ball (by linarith)
  refine ⟨A, hA, d / 4, by positivity, fun p hp ↦ (hball p (hsub hp)).1,
    transportAbsoluteJacobian slice Y₀ p₀ / 2, half_pos hpos,
    fun p hp ↦ (hball p (hsub hp)).2.1.le,
    fun p hp ↦ (hball p (hsub hp)).2.2.le, ?_⟩
  apply (hdet.mono (fun p hp ↦ (hball p (hsub (ball_subset_closedBall hp))).1)).abs
  intro p hp
  exact abs_pos.mp (half_pos hpos |>.trans
    (hball p (hsub (ball_subset_closedBall hp))).2.2)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
