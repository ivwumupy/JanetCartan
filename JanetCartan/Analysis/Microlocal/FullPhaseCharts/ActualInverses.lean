module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualInverses.ReferenceVariation
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Annulus
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.Epsilon

/-!
# Actual common full and transverse inverse charts

The geometric conclusions of `app:ch_seed:prop:seed-phase-charts` for the
literal current Hamilton phase. All domains, buffers, Jacobian gaps and
comparison thresholds precede the current frame. Every analytic input to the
conditional inverse theorem is proved here from primitive frame closeness.
The higher inverse/epsilon tame estimates are a separate obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.FullPhaseCharts.ActualInverses
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase
open ActualComparison

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Construct both common inverse charts and the full annular range for the
SAME actual Hamilton phase. The only current-frame premise is primitive
`C⁶` closeness. The open epsilon interval contains both endpoints of the
closed core `[-e,e]`. The radius `r` and epsilon radius `e` obey prescribed positive caps. The data core has radius `r`, its inverse takes values
in the open radius-`2r` chart, and injectivity/Jacobian bounds hold on the
whole closed radius-`2r` chart (`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_actual_buffered_inverses_with_caps {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0) {rmax : ℝ} (hrmax : 0 < rmax) {emax : ℝ} (hemax : 0 < emax) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let G := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ s > (0 : ℝ), s ≤ r ∧
    3 * r < T.family.radius / 8 ∧
    (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ e > (0 : ℝ), e ≤ emax ∧ ∃ δ > (0 : ℝ),
    ∃ cF > (0 : ℝ), ∃ bF > (0 : ℝ), ∃ VF LF : Set (ℝ × Euclidean (n - 1)),
    ∃ cT > (0 : ℝ), ∃ bT > (0 : ℝ), ∃ VT LT : Set (Euclidean (n - 1)),
    ∃ A > (0 : ℝ), ∃ B > (0 : ℝ),
      IsOpen VF ∧ IsCompact (closure VF) ∧ IsCompact LF ∧ LF ⊆ VF ∧
      IsOpen VT ∧ IsCompact (closure VT) ∧ IsCompact LT ∧ LT ⊆ VT ∧
      ∀ Q,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < δ →
        ContDiffOn ℝ ∞ (Function.uncurry (fullChartFamily (current T Q) (spatialCarrier T)))
          (fullParameterSet z₀ s (2 * e) ×ˢ dataSet z₀ ηb (3 * r)) ∧
        ContDiffOn ℝ ∞ (Function.uncurry (transverseChartFamily (current T Q) (spatialCarrier T)))
          (transverseParameterSet z₀ s (2 * e) ×ˢ ball ηb (3 * r)) ∧
        (∀ p ∈ fullParameterSet z₀ s (2 * e), ∀ u ∈ dataBox z₀ ηb (2 * r),
          ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
            (fderiv ℝ (fullChartFamily (current T Q) (spatialCarrier T) p) u) -
            ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
        (∀ p ∈ transverseParameterSet z₀ s (2 * e), ∀ η ∈ closedBall ηb (2 * r),
          ‖fderiv ℝ (transverseChartFamily (current T Q) (spatialCarrier T) p) η -
            ContinuousLinearMap.id ℝ (Euclidean (n - 1))‖ ≤ 1 / 4) ∧
        BufferedPhaseInverse (fullChartFamily (current T Q) (spatialCarrier T))
          (fullParameterSet z₀ s (2 * e))
          (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r))
          VF LF bF cF G ∧
        BufferedPhaseInverse (transverseChartFamily (current T Q) (spatialCarrier T))
          (transverseParameterSet z₀ s (2 * e))
          (closedBall ηb r) (ball ηb (2 * r)) (closedBall ηb (2 * r))
          VT LT bT cT (ContinuousLinearEquiv.refl ℝ (Euclidean (n - 1))) ∧
        ContDiffOn ℝ ∞ (fun q :
            (ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean (n - 1)) ×
              WithLp 2 (ℝ × Euclidean (n - 1))) × (ℝ × Euclidean (n - 1)) ↦
          deriv (fun ε ↦ phaseChartInverse (fullChartFamily (current T Q) (spatialCarrier T))
            (dataSet z₀ ηb (2 * r)) (ε,q.1.2) q.2) q.1.1)
          (fullParameterSet z₀ s (2 * e) ×ˢ VF) ∧
        ContDiffOn ℝ ∞ (fun q :
            (ℝ × Euclidean 2 × ℝ × ℝ × Euclidean (n - 1) × Euclidean (n - 1)) ×
              Euclidean (n - 1) ↦
          deriv (fun ε ↦ phaseChartInverse (transverseChartFamily (current T Q) (spatialCarrier T))
            (ball ηb (2 * r)) (ε,q.1.2) q.2) q.1.1)
          (transverseParameterSet z₀ s (2 * e) ×ˢ VT) ∧
        ∀ p ∈ fullParameterSet z₀ s (2 * e), ∀ u ∈ dataBox z₀ ηb (2 * r),
          ‖(fullChartFamily (current T Q) (spatialCarrier T) p u).2 - u.2‖ ≤ ‖u.2‖ / 2 ∧
          A ≤ ‖fullChartFamily (current T Q) (spatialCarrier T) p u‖ ∧
          ‖fullChartFamily (current T Q) (spatialCarrier T) p u‖ ≤ B := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  let G := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
  let f₀ := frozenChart (fun t ↦ gradient (dispersion T)
    (spatialCarrier T (spectatorCenter z₀,t)))
  have hη : 0 < ‖ηb‖ := norm_pos_iff.mpr
    (FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc)
  obtain ⟨ρ₀, hρ₀, hboxes⟩ := exists_actual_chart_comparison T hP hz₀ ηb
  obtain ⟨d, hdpos, hgap⟩ := FrozenIncidence.exists_reference_quarter_gap T hP hz₀ hinc hd
  let r₀ := min ρ₀ (min (d / 4) (‖ηb‖ / 8))
  let r := min rmax r₀
  have hr₀ : 0 < r₀ := lt_min hρ₀ (lt_min (by positivity) (by positivity))
  have hr : 0 < r := lt_min hrmax hr₀
  have hrr₀ : r ≤ r₀ := min_le_right _ _
  have hrρ : r ≤ ρ₀ := hrr₀.trans (min_le_left _ _)
  have hrd : 2 * r < d := by
    have := hrr₀.trans ((min_le_right ρ₀ (min (d / 4) (‖ηb‖ / 8))).trans (min_le_left _ _))
    change r ≤ d / 4 at this
    linarith
  have hrη : 2 * r ≤ ‖ηb‖ / 2 := by
    have := hrr₀.trans ((min_le_right ρ₀ (min (d / 4) (‖ηb‖ / 8))).trans (min_le_right _ _))
    change r ≤ ‖ηb‖ / 8 at this
    linarith
  obtain ⟨hphys, hcarrier, e₀, he₀, hsmooth, hcomparison⟩ := hboxes r hr hrρ
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
  have hf₀ : ∀ u ∈ dataBox z₀ ηb (2 * r), DifferentiableAt ℝ f₀ u := by
    intro u hu
    have hm : carrierParameters (spectatorCenter z₀,u.1) ∈ parameterInterior (2 * P.radius) :=
      hcarrier₂ (show (spectatorCenter z₀,u.1) ∈ closedBall (spectatorCenter z₀) (2 * r) ×ˢ
        closedBall (z₀ 0) (2 * r) from ⟨mem_closedBall_self (by positivity), hu.1⟩)
    exact ((frozenChart_contDiffAt T hP (q := (spectatorCenter z₀,u)) hm).comp u
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hgap₀ : ∀ u ∈ dataBox z₀ ηb (2 * r),
      ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
        (fderiv ℝ f₀ u) - ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 4 := by
    intro u hu
    apply (hgap (spectatorCenter z₀,u) _).2
    change dist (spectatorCenter z₀,u)
      (spectatorCenter z₀,(z₀ 0,ηb)) < d
    simp only [Prod.dist_eq, dist_self, max_lt_iff]
    exact ⟨hdpos, (mem_closedBall.mp hu.1).trans_lt hrd,
      (mem_closedBall.mp hu.2).trans_lt hrd⟩
  obtain ⟨cF, hcF, bF, hbF, VF, LF, hVF, hVFc, hLFc, hLFV, hfull⟩ :=
    exists_fullChart_inverseFamily (P := Euclidean 2)
      (dataBox_geometry z₀ ηb hr).1 (isOpen_dataSet z₀ ηb (2 * r))
      (dataBox_geometry z₀ ηb hr).2.2.2
      (prod_mono ball_subset_closedBall ball_subset_closedBall)
      ((convex_closedBall _ _).prod (convex_closedBall _ _)) G hf₀ hgap₀
  obtain ⟨cT, hcT, bT, hbT, VT, LT, hVT, hVTc, hLTc, hLTV, htrans⟩ :=
    exists_transverseChart_inverseFamily (P := Euclidean 2)
      (isCompact_closedBall ηb r) isOpen_ball
      (closedBall_subset_ball (by linarith : r < 2 * r)) ball_subset_closedBall
      (convex_closedBall ηb (2 * r))
  let N := ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1)))‖
  have hN : 0 ≤ N := norm_nonneg _
  let τ := min (bF / 2) (min bT (min (1 / (8 * (N + 1))) (min (1 / 4) (‖ηb‖ / 4))))
  have hτ : 0 < τ := lt_min (by positivity)
    (lt_min hbT (lt_min (by positivity) (lt_min (by norm_num) (by positivity))))
  have hτF : 2 * τ ≤ bF := by
    have ht : τ ≤ bF / 2 := min_le_left _ _
    linarith
  have hτT : τ ≤ bT := (min_le_right _ _).trans (min_le_left _ _)
  have hτN : N * (2 * τ) ≤ 1 / 4 := by
    have ht : τ ≤ 1 / (8 * (N + 1)) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have ht' := (le_div_iff₀ (by positivity : 0 < 8 * (N + 1))).mp ht
    nlinarith
  have hτquarter : τ ≤ 1 / 4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hτη : τ ≤ ‖ηb‖ / 4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨s₀, hs₀, _, hvariation⟩ := exists_frozen_spectator_radius T hP z₀ ηb
    (by positivity : 0 < 2 * r) hcarrier₂ hτ
  let s := min r s₀
  have hs : 0 < s := lt_min hr hs₀
  have hsr : s ≤ r := min_le_left _ _
  have hss : s ≤ s₀ := min_le_right _ _
  obtain ⟨δ, hδ, e₁, he₁, hee₁, hcomp₁⟩ := hcomparison τ hτ
  let e := min emax e₁
  have he : 0 < e := lt_min hemax he₁
  have he₁' : e ≤ e₁ := min_le_right _ _
  have hee : 2 * e < e₀ := by linarith
  have hcomp := fun Q hQ ε (hε : |ε| ≤ 2 * e) ↦
    hcomp₁ Q hQ ε (hε.trans (by linarith : 2 * e ≤ 2 * e₁))
  have hcont : ContinuousOn (fun q : Euclidean 2 × (ℝ × Euclidean (n - 1)) ↦
      frozenChart (fun t ↦ gradient (dispersion T) (spatialCarrier T (q.1,t))) q.2)
      (closedBall (spectatorCenter z₀) (2 * r) ×ˢ dataBox z₀ ηb (2 * r)) := by
    intro q hq
    have hm : carrierParameters (q.1,q.2.1) ∈ parameterInterior (2 * P.radius) :=
      hcarrier₂ (show (q.1,q.2.1) ∈ closedBall (spectatorCenter z₀) (2 * r) ×ˢ
        closedBall (z₀ 0) (2 * r) from ⟨hq.1,hq.2.1⟩)
    exact (frozenChart_contDiffAt T hP (q := q) hm).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := ((isCompact_closedBall _ _).prod
    (dataBox_geometry z₀ ηb (by positivity : 0 < 2 * r)).1).exists_bound_of_continuousOn hcont
  refine ⟨r, hr, min_le_left _ _, s, hs, hsr, hphys, hcarrier, e, he, min_le_left _ _, δ, hδ, cF, hcF, bF, hbF, VF, LF,
    cT, hcT, bT, hbT, VT, LT, ‖ηb‖ / 4, by positivity,
    |M| + ‖ηb‖ + 1, by positivity,
    hVF, hVFc, hLFc, hLFV, hVT, hVTc, hLTc, hLTV, ?_⟩
  intro Q hQ
  have hp₂ : fullParameterSet (n := n) z₀ s (2 * e) ⊆ fullParameterSet z₀ (2 * r) (2 * e) := by
    intro p hp
    exact ⟨hp.1, ball_subset_ball (by linarith) hp.2.1,
      ball_subset_ball (by linarith) hp.2.2.1, ball_subset_ball (by linarith) hp.2.2.2⟩
  have hp₃ : fullParameterSet (n := n) z₀ s (2 * e) ⊆ fullParameterSet z₀ (3 * r) e₀ := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      ball_subset_ball (by linarith) hp.2.1,
      ball_subset_ball (by linarith) hp.2.2.1, ball_subset_ball (by linarith) hp.2.2.2⟩
  have ht₂ : transverseParameterSet (n := n) z₀ s (2 * e) ⊆
      transverseParameterSet z₀ (2 * r) (2 * e) := by
    intro p hp
    exact ⟨hp.1, ball_subset_ball (by linarith) hp.2.1,
      ball_subset_ball (by linarith) hp.2.2.1,
      ball_subset_ball (by linarith) hp.2.2.2.1, ball_subset_ball (by linarith) hp.2.2.2.2⟩
  have ht₃ : transverseParameterSet (n := n) z₀ s (2 * e) ⊆
      transverseParameterSet z₀ (3 * r) e₀ := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      ball_subset_ball (by linarith) hp.2.1,
      ball_subset_ball (by linarith) hp.2.2.1,
      ball_subset_ball (by linarith) hp.2.2.2.1, ball_subset_ball (by linarith) hp.2.2.2.2⟩
  have hc := fullChartComparison_on_open_parameters T Q
    (fun ε hε ↦ (hcomp Q hQ ε hε).1)
  have hct := transverseChartComparison_on_open_parameters T Q
    (fun ε hε ↦ (hcomp Q hQ ε hε).2)
  have hvary (p) (hp : p ∈ fullParameterSet (n := n) z₀ s (2 * e))
      (u) (hu : u ∈ dataBox z₀ ηb (2 * r)) :=
    hvariation p.2.1 (closedBall_subset_closedBall hss (ball_subset_closedBall hp.2.1)) u hu
  have hnear : ∀ p ∈ fullParameterSet z₀ s (2 * e),
      ∀ u ∈ dataBox z₀ ηb (2 * r),
      ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
        (fderiv ℝ (fullChartFamily (current T Q) (spatialCarrier T) p) u -
          fderiv ℝ f₀ u)‖ ≤ 1 / 4 := by
    intro p hp u hu
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply (mul_le_mul_of_nonneg_left _ hN).trans hτN
    have hh := (norm_sub_le_norm_sub_add_norm_sub
      (fderiv ℝ (fullChartFamily (current T Q) (spatialCarrier T) p) u)
      (fderiv ℝ (frozenChart (fun t ↦ gradient (dispersion T)
        (spatialCarrier T (p.2.1,t)))) u) (fderiv ℝ f₀ u)).trans
        (add_le_add (hc p (hp₂ hp) u hu).2.le (hvary p hp u hu).2.le)
    simpa only [two_mul] using hh
  have htransgap : ∀ p ∈ transverseParameterSet z₀ s (2 * e),
      ∀ η ∈ closedBall ηb (2 * r),
      ‖fderiv ℝ (transverseChartFamily (current T Q) (spatialCarrier T) p) η -
        ContinuousLinearMap.id ℝ (Euclidean (n - 1))‖ ≤ 1 / 4 :=
    fun p hp η hη ↦ (hct p (ht₂ hp) η hη).2.le.trans hτquarter
  have hFull : BufferedPhaseInverse
      (fullChartFamily (current T Q) (spatialCarrier T))
      (fullParameterSet z₀ s (2 * e)) (dataBox z₀ ηb r)
      (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) VF LF bF cF G := by
    apply hfull (current T Q) (spatialCarrier T)
      (fullParameterSet z₀ s (2 * e)) (dataSet z₀ ηb (3 * r))
      (isOpen_fullParameterSet _ _ _) (isOpen_dataSet _ _ _)
      (prod_mono (closedBall_subset_ball (by linarith))
        (closedBall_subset_ball (by linarith)))
      ((hsmooth Q).1.mono (prod_mono hp₃ Subset.rfl)) hnear
    intro p hp u hu
    have hu' : u ∈ dataBox z₀ ηb (2 * r) :=
      ⟨closedBall_subset_closedBall (by linarith) hu.1,
        closedBall_subset_closedBall (by linarith) hu.2⟩
    exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add
        (hc p (hp₂ hp) u hu').1.le (hvary p hp u hu').1.le)).trans (by linarith)
  have hTrans : BufferedPhaseInverse
      (transverseChartFamily (current T Q) (spatialCarrier T))
      (transverseParameterSet z₀ s (2 * e)) (closedBall ηb r)
      (ball ηb (2 * r)) (closedBall ηb (2 * r)) VT LT bT cT
      (ContinuousLinearEquiv.refl ℝ (Euclidean (n - 1))) := by
    apply htrans (current T Q) (spatialCarrier T)
      (transverseParameterSet z₀ s (2 * e)) (ball ηb (3 * r))
      (isOpen_transverseParameterSet _ _ _) isOpen_ball
      (closedBall_subset_ball (by linarith))
      ((hsmooth Q).2.2.mono (prod_mono ht₃ Subset.rfl))
    · intro p hp η hη
      exact (hct p (ht₂ hp) η hη).2.le.trans hτquarter
    · intro p hp η hη
      exact (hct p (ht₂ hp) η (closedBall_subset_closedBall (by linarith) hη)).1.le.trans hτT
  refine ⟨(hsmooth Q).2.1.mono (prod_mono hp₃ Subset.rfl),
    (hsmooth Q).2.2.mono (prod_mono ht₃ Subset.rfl),
    fun p hp u hu ↦ normalized_derivative_gap_of_perturbation G (hgap₀ u hu) (hnear p hp u hu),
    htransgap, hFull, hTrans,
    InverseEstimates.contDiffOn_deriv_epsilon ((isOpen_fullParameterSet _ _ _).prod hVF) hFull.smooth,
    InverseEstimates.contDiffOn_deriv_epsilon ((isOpen_transverseParameterSet _ _ _).prod hVT) hTrans.smooth,
    ?_⟩
  intro p hp u hu
  have hclose := (hc p (hp₂ hp) u hu).1.le
  have hηu : ‖ηb‖ / 2 ≤ ‖u.2‖ := by
    have huη : ‖u.2 - ηb‖ ≤ 2 * r := mem_closedBall_iff_norm.mp hu.2
    have hn := norm_le_insert' ηb u.2
    rw [norm_sub_rev ηb u.2] at hn
    linarith
  have hrelative : ‖(fullChartFamily (current T Q) (spatialCarrier T) p u).2 - u.2‖ ≤ ‖u.2‖ / 2 :=
    (norm_snd_le (_ - frozenChart (fun t ↦ gradient (dispersion T)
      (spatialCarrier T (p.2.1,t))) u)).trans (hclose.trans (by linarith))
  refine ⟨hrelative, (by linarith : ‖ηb‖ / 4 ≤ ‖u.2‖ / 2).trans
    (norm_lower_of_transverse_close _ _ hrelative), ?_⟩
  have hm := hM (p.2.1,u) ⟨ball_subset_closedBall (hp₂ hp).2.1,hu⟩
  have hn := norm_le_insert' (fullChartFamily (current T Q) (spatialCarrier T) p u)
    (frozenChart (fun t ↦ gradient (dispersion T) (spatialCarrier T (p.2.1,t))) u)
  linarith [le_abs_self M]

/-- The actual construction with an arbitrary data-radius cap. The stronger
`exists_actual_buffered_inverses_with_caps` also caps epsilon before the current
frame (`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_actual_buffered_inverses_below {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0) {rmax : ℝ} (hrmax : 0 < rmax) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let G := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ s > (0 : ℝ), s ≤ r ∧
    3 * r < T.family.radius / 8 ∧
    (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ e > (0 : ℝ), ∃ δ > (0 : ℝ),
    ∃ cF > (0 : ℝ), ∃ bF > (0 : ℝ), ∃ VF LF : Set (ℝ × Euclidean (n - 1)),
    ∃ cT > (0 : ℝ), ∃ bT > (0 : ℝ), ∃ VT LT : Set (Euclidean (n - 1)),
    ∃ A > (0 : ℝ), ∃ B > (0 : ℝ),
      IsOpen VF ∧ IsCompact (closure VF) ∧ IsCompact LF ∧ LF ⊆ VF ∧
      IsOpen VT ∧ IsCompact (closure VT) ∧ IsCompact LT ∧ LT ⊆ VT ∧
      ∀ Q,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < δ →
        ContDiffOn ℝ ∞ (Function.uncurry (fullChartFamily (current T Q) (spatialCarrier T)))
          (fullParameterSet z₀ s (2 * e) ×ˢ dataSet z₀ ηb (3 * r)) ∧
        ContDiffOn ℝ ∞ (Function.uncurry (transverseChartFamily (current T Q) (spatialCarrier T)))
          (transverseParameterSet z₀ s (2 * e) ×ˢ ball ηb (3 * r)) ∧
        (∀ p ∈ fullParameterSet z₀ s (2 * e), ∀ u ∈ dataBox z₀ ηb (2 * r),
          ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
            (fderiv ℝ (fullChartFamily (current T Q) (spatialCarrier T) p) u) -
            ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
        (∀ p ∈ transverseParameterSet z₀ s (2 * e), ∀ η ∈ closedBall ηb (2 * r),
          ‖fderiv ℝ (transverseChartFamily (current T Q) (spatialCarrier T) p) η -
            ContinuousLinearMap.id ℝ (Euclidean (n - 1))‖ ≤ 1 / 4) ∧
        BufferedPhaseInverse (fullChartFamily (current T Q) (spatialCarrier T))
          (fullParameterSet z₀ s (2 * e))
          (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r))
          VF LF bF cF G ∧
        BufferedPhaseInverse (transverseChartFamily (current T Q) (spatialCarrier T))
          (transverseParameterSet z₀ s (2 * e))
          (closedBall ηb r) (ball ηb (2 * r)) (closedBall ηb (2 * r))
          VT LT bT cT (ContinuousLinearEquiv.refl ℝ (Euclidean (n - 1))) ∧
        ContDiffOn ℝ ∞ (fun q :
            (ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean (n - 1)) ×
              WithLp 2 (ℝ × Euclidean (n - 1))) × (ℝ × Euclidean (n - 1)) ↦
          deriv (fun ε ↦ phaseChartInverse (fullChartFamily (current T Q) (spatialCarrier T))
            (dataSet z₀ ηb (2 * r)) (ε,q.1.2) q.2) q.1.1)
          (fullParameterSet z₀ s (2 * e) ×ˢ VF) ∧
        ContDiffOn ℝ ∞ (fun q :
            (ℝ × Euclidean 2 × ℝ × ℝ × Euclidean (n - 1) × Euclidean (n - 1)) ×
              Euclidean (n - 1) ↦
          deriv (fun ε ↦ phaseChartInverse (transverseChartFamily (current T Q) (spatialCarrier T))
            (ball ηb (2 * r)) (ε,q.1.2) q.2) q.1.1)
          (transverseParameterSet z₀ s (2 * e) ×ˢ VT) ∧
        ∀ p ∈ fullParameterSet z₀ s (2 * e), ∀ u ∈ dataBox z₀ ηb (2 * r),
          ‖(fullChartFamily (current T Q) (spatialCarrier T) p u).2 - u.2‖ ≤ ‖u.2‖ / 2 ∧
          A ≤ ‖fullChartFamily (current T Q) (spatialCarrier T) p u‖ ∧
          ‖fullChartFamily (current T Q) (spatialCarrier T) p u‖ ≤ B := by
  obtain ⟨r, hr, hrmax', s, hs, hsr, hp, hc, e, he, _, hrest⟩ :=
    exists_actual_buffered_inverses_with_caps T hP hz₀ hk hinc hd hrmax
      (show (0 : ℝ) < 1 by norm_num)
  exact ⟨r, hr, hrmax', s, hs, hsr, hp, hc, e, he, hrest⟩

/-- The actual buffered chart construction without a prescribed radius cap.
This retains the original geometric interface; `exists_actual_buffered_inverses_below`
allows its quantitative consumer to fit the charts into primitive integration balls
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_actual_buffered_inverses {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let G := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
    ∃ r > (0 : ℝ), ∃ s > (0 : ℝ), s ≤ r ∧
    3 * r < T.family.radius / 8 ∧
    (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ e > (0 : ℝ), ∃ δ > (0 : ℝ),
    ∃ cF > (0 : ℝ), ∃ bF > (0 : ℝ), ∃ VF LF : Set (ℝ × Euclidean (n - 1)),
    ∃ cT > (0 : ℝ), ∃ bT > (0 : ℝ), ∃ VT LT : Set (Euclidean (n - 1)),
    ∃ A > (0 : ℝ), ∃ B > (0 : ℝ),
      IsOpen VF ∧ IsCompact (closure VF) ∧ IsCompact LF ∧ LF ⊆ VF ∧
      IsOpen VT ∧ IsCompact (closure VT) ∧ IsCompact LT ∧ LT ⊆ VT ∧
      ∀ Q,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < δ →
        ContDiffOn ℝ ∞ (Function.uncurry (fullChartFamily (current T Q) (spatialCarrier T)))
          (fullParameterSet z₀ s (2 * e) ×ˢ dataSet z₀ ηb (3 * r)) ∧
        ContDiffOn ℝ ∞ (Function.uncurry (transverseChartFamily (current T Q) (spatialCarrier T)))
          (transverseParameterSet z₀ s (2 * e) ×ˢ ball ηb (3 * r)) ∧
        (∀ p ∈ fullParameterSet z₀ s (2 * e), ∀ u ∈ dataBox z₀ ηb (2 * r),
          ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
            (fderiv ℝ (fullChartFamily (current T Q) (spatialCarrier T) p) u) -
            ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
        (∀ p ∈ transverseParameterSet z₀ s (2 * e), ∀ η ∈ closedBall ηb (2 * r),
          ‖fderiv ℝ (transverseChartFamily (current T Q) (spatialCarrier T) p) η -
            ContinuousLinearMap.id ℝ (Euclidean (n - 1))‖ ≤ 1 / 4) ∧
        BufferedPhaseInverse (fullChartFamily (current T Q) (spatialCarrier T))
          (fullParameterSet z₀ s (2 * e))
          (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r))
          VF LF bF cF G ∧
        BufferedPhaseInverse (transverseChartFamily (current T Q) (spatialCarrier T))
          (transverseParameterSet z₀ s (2 * e))
          (closedBall ηb r) (ball ηb (2 * r)) (closedBall ηb (2 * r))
          VT LT bT cT (ContinuousLinearEquiv.refl ℝ (Euclidean (n - 1))) ∧
        ContDiffOn ℝ ∞ (fun q :
            (ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean (n - 1)) ×
              WithLp 2 (ℝ × Euclidean (n - 1))) × (ℝ × Euclidean (n - 1)) ↦
          deriv (fun ε ↦ phaseChartInverse (fullChartFamily (current T Q) (spatialCarrier T))
            (dataSet z₀ ηb (2 * r)) (ε,q.1.2) q.2) q.1.1)
          (fullParameterSet z₀ s (2 * e) ×ˢ VF) ∧
        ContDiffOn ℝ ∞ (fun q :
            (ℝ × Euclidean 2 × ℝ × ℝ × Euclidean (n - 1) × Euclidean (n - 1)) ×
              Euclidean (n - 1) ↦
          deriv (fun ε ↦ phaseChartInverse (transverseChartFamily (current T Q) (spatialCarrier T))
            (ball ηb (2 * r)) (ε,q.1.2) q.2) q.1.1)
          (transverseParameterSet z₀ s (2 * e) ×ˢ VT) ∧
        ∀ p ∈ fullParameterSet z₀ s (2 * e), ∀ u ∈ dataBox z₀ ηb (2 * r),
          ‖(fullChartFamily (current T Q) (spatialCarrier T) p u).2 - u.2‖ ≤ ‖u.2‖ / 2 ∧
          A ≤ ‖fullChartFamily (current T Q) (spatialCarrier T) p u‖ ∧
          ‖fullChartFamily (current T Q) (spatialCarrier T) p u‖ ≤ B := by
  obtain ⟨r, hr, _, hrest⟩ := exists_actual_buffered_inverses_below T hP hz₀ hk hinc hd
    (show (0 : ℝ) < 1 by norm_num)
  exact ⟨r, hr, hrest⟩

end JanetCartan.FullPhaseCharts.ActualInverses
