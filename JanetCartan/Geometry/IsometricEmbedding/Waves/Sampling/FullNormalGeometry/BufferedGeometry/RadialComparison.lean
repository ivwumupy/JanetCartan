module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.BufferedGeometry.RadialComparison.Scaling
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualInverses.ReferenceVariation

/-!
# Uniform C¹ comparison on the complete radial sampling support

For the SAME retained Hamilton family, transfer the actual normalized-box
comparison through the exact radial quotient law, including epsilon zero.
Freeze the spectators using the actual dispersion, then bound the inverse
radial coordinate differential uniformly on the prescribed positive interval.

The resulting arbitrarily shrinkable radius constructor supplies the actual
perturbation input to inverse stability for the full sampling geometry of
`app:ch_seed:prop:seed-phase-charts`. All thresholds precede the current frame,
epsilon, physical endpoints and spectators. The primitive coefficient domain
is unchanged; neither an inverse nor chart-error bounds are assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.FullNormalGeometry
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison ActualInverses
open ContinuumNormalReduction.ConicChart RadialComparison

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Arbitrarily small data radii admit uniform actual C¹ comparison over the
ENTIRE compact radial support. For each tolerance and epsilon cap, choose the
spectator/physical radius, epsilon radius and primitive whole-frame C⁶ threshold
before the current frame and all chart parameters. The comparison map is the
actual frozen dispersion at the fixed spectator center.

This is the perturbation producer for the full sampling buffered inverse
construction (`app:ch_seed:prop:seed-phase-charts`). The transfer uses epsilon
`epsilon * a`, as required by `app:ch_seed:eq:seed-quotient-integral`, rather
than homogeneity of the nonlinear phase at fixed epsilon. -/
theorem exists_actual_radial_chart_comparison {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    (ηb : Euclidean m) {amin amax : ℝ} (hamin : 0 < amin) (ha : amin ≤ amax) :
    ∃ r₀ > (0 : ℝ), ∀ r, 0 < r → r ≤ r₀ →
      ∀ τ, 0 < τ → ∀ emax, 0 < emax →
      ∃ s > (0 : ℝ), s ≤ r ∧ ∃ e > (0 : ℝ), e ≤ emax ∧ ∃ δ > (0 : ℝ),
        ∀ Q,
          cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
            (Q.1 - fun _ ↦ cubeStress (m + 1)) < δ →
        ∀ p ∈ fullParameterSet z₀ s (2 * e),
          ∀ u ∈ (fun a : ℝ × (ℝ × Euclidean m) ↦ radialScale a.1 a.2) ''
            (Icc amin amax ×ˢ dataBox (n := m + 1) z₀ ηb (2 * r)),
          let f := fullChartFamily (current T Q) (spatialCarrier T) p
          let f₀ := frozenChart (fun t ↦ gradient (dispersion T)
            (spatialCarrier T (spectatorCenter z₀,t)))
          DifferentiableAt ℝ f u ∧ ‖f u - f₀ u‖ ≤ τ ∧
            ‖fderiv ℝ f u - fderiv ℝ f₀ u‖ ≤ τ := by
  obtain ⟨r₀, hr₀, hboxes⟩ := exists_actual_chart_comparison T hP hz₀ ηb
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr hrr τ hτ emax hemax
  have hamax : 0 < amax := hamin.trans_le ha
  let M := 1 + amin⁻¹
  have hM : 0 < M := by dsimp [M]; positivity
  have hMone : 1 ≤ M := by dsimp [M]; linarith [inv_pos.mpr hamin]
  -- Split the normalized error between frame comparison and spectator variation.
  let σ := τ / (2 * amax * M)
  have hσ : 0 < σ := div_pos hτ (by positivity)
  have hbudget : amax * (2 * σ) * M = τ := by
    dsimp [σ]
    field_simp
  have hvalueBudget : amax * (2 * σ) ≤ τ := by
    calc
      _ ≤ amax * (2 * σ) * M := le_mul_of_one_le_right (by positivity) hMone
      _ = τ := hbudget
  obtain ⟨_, hcarrier, e₀, _, hsmooth, hcomparison⟩ := hboxes r hr hrr
  have hcarrier₂ : closedBall (spectatorCenter z₀) (2 * r) ×ˢ
      closedBall (z₀ 0) (2 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (2 * P.radius) := by
    intro q hq
    have hm : carrierParameters q ∈ parameterInterior (3 * P.radius / 2) :=
      hcarrier (show q ∈ closedBall (spectatorCenter z₀) (3 * r) ×ˢ
        closedBall (z₀ 0) (3 * r) from
        ⟨closedBall_subset_closedBall (by linarith) hq.1,
          closedBall_subset_closedBall (by linarith) hq.2⟩)
    exact fun i ↦ (hm i).trans_le (by linarith [hP.1])
  obtain ⟨s₀, hs₀, _, hvariation⟩ := exists_frozen_spectator_radius T hP z₀ ηb
    (by positivity : 0 < 2 * r) hcarrier₂ hσ
  let s := min r s₀
  have hs : 0 < s := lt_min hr hs₀
  have hsr : s ≤ r := min_le_left _ _
  have hss : s ≤ s₀ := min_le_right _ _
  obtain ⟨δ, hδ, e₁, he₁, hee₁, hcomp⟩ := hcomparison σ hσ
  -- Every shifted epsilon remains in the SAME normalized comparison interval.
  let e := min emax (e₁ / amax)
  have he : 0 < e := lt_min hemax (div_pos he₁ hamax)
  have heamax : e * amax ≤ e₁ :=
    (le_div_iff₀ hamax).mp (min_le_right _ _)
  refine ⟨s, hs, hsr, e, he, min_le_left _ _, δ, hδ, ?_⟩
  intro Q hQ p hp u hu
  obtain ⟨⟨a,w⟩, ⟨ha', hw⟩, rfl⟩ := hu
  dsimp only
  have hapos : 0 < a := hamin.trans_le ha'.1
  have hεa : |p.1 * a| < 2 * e₁ := by
    calc
      |p.1 * a| = |p.1| * a := by rw [abs_mul, abs_of_pos hapos]
      _ < (2 * e) * a := mul_lt_mul_of_pos_right (abs_lt.mpr hp.1) hapos
      _ ≤ 2 * e₁ := by nlinarith [mul_le_mul_of_nonneg_left ha'.2 he.le]
  have hp₂ : (p.1 * a, p.2) ∈ fullParameterSet (n := m + 1) z₀ (2 * r) (2 * e₁) :=
    ⟨abs_lt.mp hεa, ball_subset_ball (by linarith) hp.2.1,
      ball_subset_ball (by linarith) hp.2.2.1, ball_subset_ball (by linarith) hp.2.2.2⟩
  have hp₃ : (p.1 * a, p.2) ∈ fullParameterSet (n := m + 1) z₀ (3 * r) e₀ :=
    ⟨abs_lt.mp (hεa.trans hee₁), ball_subset_ball (by linarith) hp.2.1,
      ball_subset_ball (by linarith) hp.2.2.1, ball_subset_ball (by linarith) hp.2.2.2⟩
  have hw₃ : w ∈ dataSet (n := m + 1) z₀ ηb (3 * r) :=
    ⟨closedBall_subset_ball (by linarith) hw.1,
      closedBall_subset_ball (by linarith) hw.2⟩
  have hdiff : DifferentiableAt ℝ
      (fullChartFamily (current T Q) (spatialCarrier T) (p.1 * a,p.2)) w := by
    have hj := (hsmooth Q).2.1.contDiffAt
      (((isOpen_fullParameterSet _ _ _).prod (isOpen_dataSet _ _ _)).mem_nhds
        (show ((p.1 * a,p.2),w) ∈ fullParameterSet (n := m + 1) z₀ (3 * r) e₀ ×ˢ
          dataSet (n := m + 1) z₀ ηb (3 * r) from ⟨hp₃,hw₃⟩))
    exact (hj.comp w (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hc := fullChartComparison_on_open_parameters T Q
    (fun ε hε ↦ (hcomp Q hQ ε hε).1) _ hp₂ w hw
  have hv := hvariation p.2.1
    (closedBall_subset_closedBall hss (ball_subset_closedBall hp.2.1)) w hw
  let f₀ := frozenChart (fun t ↦ gradient (dispersion T)
    (spatialCarrier T (spectatorCenter z₀,t)))
  let g := fullChartFamily (current T Q) (spatialCarrier T) (p.1 * a,p.2)
  have hval : ‖g w - f₀ w‖ ≤ 2 * σ := by
    calc
      _ ≤ ‖g w - frozenChart (fun t ↦ gradient (dispersion T)
          (spatialCarrier T (p.2.1,t))) w‖ +
          ‖frozenChart (fun t ↦ gradient (dispersion T)
          (spatialCarrier T (p.2.1,t))) w - f₀ w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ σ + σ := add_le_add hc.1.le hv.1.le
      _ = 2 * σ := by ring
  have hder : ‖fderiv ℝ g w - fderiv ℝ f₀ w‖ ≤ 2 * σ := by
    calc
      _ ≤ ‖fderiv ℝ g w - fderiv ℝ (frozenChart (fun t ↦ gradient (dispersion T)
          (spatialCarrier T (p.2.1,t)))) w‖ +
          ‖fderiv ℝ (frozenChart (fun t ↦ gradient (dispersion T)
          (spatialCarrier T (p.2.1,t)))) w - fderiv ℝ f₀ w‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ σ + σ := add_le_add hc.2.le hv.2.le
      _ = 2 * σ := by ring
  refine ⟨differentiableAt_fullChartFamily_radialScale T Q p hapos.ne' hdiff, ?_, ?_⟩
  · rw [fullChartFamily_radialScale, frozenChart_radialScale, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos hapos]
    exact (mul_le_mul ha'.2 hval (norm_nonneg _) hamax.le).trans hvalueBudget
  · rw [fderiv_fullChartFamily_radialScale T Q p hapos.ne',
      fderiv_frozenChart_radialScale _ hapos.ne']
    change ‖a • ((fderiv ℝ g w).comp (radialLinearMap (E := Euclidean m) a⁻¹)) -
      a • ((fderiv ℝ f₀ w).comp (radialLinearMap (E := Euclidean m) a⁻¹))‖ ≤ τ
    have heq : a • ((fderiv ℝ g w).comp (radialLinearMap (E := Euclidean m) a⁻¹)) -
        a • ((fderiv ℝ f₀ w).comp (radialLinearMap (E := Euclidean m) a⁻¹)) =
        a • ((fderiv ℝ g w - fderiv ℝ f₀ w).comp
          (radialLinearMap (E := Euclidean m) a⁻¹)) := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [sub_apply, smul_apply,
        ContinuousLinearMap.comp_apply, smul_sub]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hapos]
    calc
      _ ≤ a * (‖fderiv ℝ g w - fderiv ℝ f₀ w‖ *
          ‖radialLinearMap (E := Euclidean m) a⁻¹‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hapos.le
      _ ≤ amax * ((2 * σ) * M) := mul_le_mul ha'.2
        (mul_le_mul hder (norm_radialLinearMap_inv_le hamin ha'.1)
          (norm_nonneg _) (by positivity)) (by positivity) hamax.le
      _ = τ := by rw [← mul_assoc, hbudget]

end JanetCartan.Sampling.FullNormalGeometry
