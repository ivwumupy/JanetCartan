module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Frozen
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ConicChart.Basic

/-!
# Triangular normalization on a complete radial interval

For `app:ch_seed:prop:seed-phase-charts`, normalizing the frozen differential
by the largest radial label gives first diagonal entry `a / amax`. Compactness
then permits one angular/incidence radius for every label in the prescribed
positive interval. The consumer is `exists_radial_frozen_derivative_gap`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped InnerProductSpace Topology NNReal

namespace JanetCartan.Sampling.FullNormalGeometry.RadialFrozen
open FullPhaseCharts ContinuumNormalReduction.ConicChart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The normalized central triangular differential has a uniform strict gap
on the full positive radial interval (`app:ch_seed:prop:seed-phase-charts`). -/
theorem norm_normalized_triangular_radial_le (v : E) {d amin amax a : ℝ}
    (hd : d ≠ 0) (hamin : 0 < amin) (ha : a ∈ Icc amin amax) :
    ‖((triangularEquiv (amax * d) v
        (mul_ne_zero (ne_of_gt (hamin.trans_le (ha.1.trans ha.2))) hd)).symm :
          (ℝ × E) →L[ℝ] (ℝ × E)).comp (triangularDifferential (a * d) v) -
      ContinuousLinearMap.id ℝ (ℝ × E)‖ ≤ 1 - amin / amax := by
  have hmax : 0 < amax := hamin.trans_le (ha.1.trans ha.2)
  have hfrac : a / amax ≤ 1 := (div_le_one hmax).mpr ha.2
  have hmin : amin / amax ≤ a / amax := div_le_div_of_nonneg_right ha.1 hmax.le
  have hnonneg : 0 ≤ 1 - amin / amax := by linarith
  apply ContinuousLinearMap.opNorm_le_bound _ hnonneg
  intro w
  have he : ((triangularEquiv (amax * d) v
        (mul_ne_zero (ne_of_gt hmax) hd)).symm :
          (ℝ × E) →L[ℝ] (ℝ × E)).comp (triangularDifferential (a * d) v) w - w =
      ((a / amax - 1) * w.1, 0) := by
    change ((amax * d)⁻¹ * ((a * d * w.1 + ⟪v, w.2⟫_ℝ) - ⟪v, w.2⟫_ℝ),
      w.2) - w = _
    apply Prod.ext
    · change (amax * d)⁻¹ * ((a * d * w.1 + ⟪v, w.2⟫_ℝ) - ⟪v, w.2⟫_ℝ) -
        w.1 = (a / amax - 1) * w.1
      field_simp
      ring
    · simp
  rw [sub_apply, ContinuousLinearMap.id_apply, he]
  rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _), norm_mul,
    Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hfrac), Real.norm_eq_abs]
  calc
    -(a / amax - 1) * |w.1| ≤ (1 - amin / amax) * |w.1| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ ≤ (1 - amin / amax) * ‖w‖ :=
      mul_le_mul_of_nonneg_left (norm_fst_le w) hnonneg

/-- A single neighborhood of the normalized data controls the frozen chart
on every radial label, without subdividing or shrinking the radial interval.
This supplies the analytic input to `exists_radial_frozen_derivative_gap`
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_frozen_radial_neighborhood {v : ℝ → E} {t₀ : ℝ} {ηb : E}
    (hv : ContDiffAt ℝ 1 v t₀) (hd : ⟪deriv v t₀, ηb⟫_ℝ ≠ 0)
    {amin amax : ℝ} (hamin : 0 < amin) (ha : amin ≤ amax) :
    ∃ ρ > 0, ∃ G : (ℝ × E) ≃L[ℝ] (ℝ × E), ∃ q : ℝ≥0, q < 1 ∧
      ∀ w ∈ ball (t₀, ηb) ρ, ∀ a ∈ Icc amin amax,
        DifferentiableAt ℝ (frozenChart v) (radialScale a w) ∧
        ‖(G.symm : (ℝ × E) →L[ℝ] (ℝ × E)).comp
            (fderiv ℝ (frozenChart v) (radialScale a w)) -
          ContinuousLinearMap.id ℝ (ℝ × E)‖ ≤ q := by
  have hmax : 0 < amax := hamin.trans_le ha
  let d := ⟪deriv v t₀, ηb⟫_ℝ
  let G := triangularEquiv (amax * d) (v t₀) (mul_ne_zero hmax.ne' hd)
  have hfracpos : 0 < amin / amax := div_pos hamin hmax
  have hfracle : amin / amax ≤ 1 := (div_le_one hmax).mpr ha
  let q : ℝ≥0 := ⟨1 - amin / (2 * amax), by
    have he : amin / (2 * amax) = (amin / amax) / 2 := by ring
    rw [he]
    linarith⟩
  have hq : q < 1 := by
    change 1 - amin / (2 * amax) < 1
    have := div_pos hamin (mul_pos (by norm_num : (0 : ℝ) < 2) hmax)
    linarith
  have hmargin : 1 - amin / amax < (q : ℝ) := by
    change 1 - amin / amax < 1 - amin / (2 * amax)
    have he : amin / (2 * amax) = (amin / amax) / 2 := by ring
    rw [he]
    linarith
  have hev : ∀ᶠ w in 𝓝 (t₀, ηb), ∀ a ∈ Icc amin amax,
      DifferentiableAt ℝ (frozenChart v) (radialScale a w) ∧
      ‖(G.symm : (ℝ × E) →L[ℝ] (ℝ × E)).comp
          (fderiv ℝ (frozenChart v) (radialScale a w)) -
        ContinuousLinearMap.id ℝ (ℝ × E)‖ < (q : ℝ) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro a ha'
    have hs : ContDiffAt ℝ 1 (frozenChart v) (radialScale a (t₀, ηb)) :=
      contDiffAt_frozenChart hv
    have hc : ContinuousAt (fun p : (ℝ × E) × ℝ ↦ radialScale p.2 p.1)
        ((t₀, ηb), a) := by
      unfold radialScale
      fun_prop
    have hnorm : ContinuousAt (fun p : (ℝ × E) × ℝ ↦
        ‖(G.symm : (ℝ × E) →L[ℝ] (ℝ × E)).comp
          (fderiv ℝ (frozenChart v) (radialScale p.2 p.1)) -
          ContinuousLinearMap.id ℝ (ℝ × E)‖) ((t₀, ηb), a) :=
      ((continuousAt_const.clm_comp
        ((hs.continuousAt_fderiv one_ne_zero).comp (f := fun p : (ℝ × E) × ℝ ↦
          radialScale p.2 p.1) hc)).sub continuousAt_const).norm
    have hcentral :
        ‖(G.symm : (ℝ × E) →L[ℝ] (ℝ × E)).comp
          (fderiv ℝ (frozenChart v) (radialScale a (t₀, ηb))) -
          ContinuousLinearMap.id ℝ (ℝ × E)‖ < (q : ℝ) := by
      rw [(hasFDerivAt_frozenChart (hv.differentiableAt one_ne_zero).hasDerivAt).fderiv]
      simp only [radialScale, inner_smul_right]
      exact (norm_normalized_triangular_radial_le (v t₀) hd hamin ha').trans_lt hmargin
    have hdiff : ∀ᶠ p : (ℝ × E) × ℝ in 𝓝 ((t₀, ηb), a),
        DifferentiableAt ℝ (frozenChart v) (radialScale p.2 p.1) :=
      (hc.eventually (hs.eventually (by norm_num))).mono
        (fun _ h ↦ h.differentiableAt one_ne_zero)
    exact hdiff.and (hnorm.eventually (gt_mem_nhds hcentral))
  obtain ⟨ρ, hρ, hb⟩ := Metric.eventually_nhds_iff_ball.mp hev
  exact ⟨ρ, hρ, G, q, hq, fun w hw a ha' ↦
    ⟨(hb w hw a ha').1, (hb w hw a ha').2.le⟩⟩

end JanetCartan.Sampling.FullNormalGeometry.RadialFrozen
