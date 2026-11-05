module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence.RetainedMaps

/-!
# Buffered characteristic charts retaining their actual autonomous lift

Construct the inverse as backward evolution of the same smooth ODE witness.
The literal formula holds globally, so downstream estimates on the entire
closed cylinder do not depend on an arbitrary extension outside the flow tube.
The common construction serves both carrier and full-modulation labels.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff NNReal

namespace JanetCartan.ContinuumRow.NormalizedChartFamily
open NullTransport.ActualFlow
open ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference

/-- Construct the buffered chart from one actual `IsSmoothFlowOn` witness,
retaining its literal forward and backward restrictions. The input is the
primitive vector-field bound, not a flow or inverse estimate. Unit time and
zero carrier velocity give the parameter identities for both kinds of null
transport. Consumers: `exists_carrier_chart_with_lift` and the full-modulation
source constructor (`app:ch_waves:thm:leading`, `app:ch_waves:eq:joint-tame`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_buffered_chart_with_lift
    {X Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {Ω : Set (ℝ × (X × Z))} {V : ℝ × (X × Z) → ℝ × (X × Z)}
    {p₀ : X × Z} {R M : ℝ}
    (hΩ : IsOpen Ω) (hbuffer : closedBall (0, p₀) R ⊆ Ω)
    (hV : ContDiffOn ℝ ∞ V Ω) (hR : 0 < R) (hM : 0 ≤ M)
    (hb : ∀ q ∈ closedBall (0, p₀) R, ‖V q‖ ≤ M ∧ ‖fderiv ℝ V q‖ ≤ M)
    (hunit : ∀ q, (V q).1 = 1) (hparameter : ∀ q, (V q).2.2 = 0) :
    ∃ Ψ : (ℝ × (X × Z)) × ℝ → ℝ × (X × Z),
      ODE.IsSmoothFlowOn V (0, p₀) R (R / 2) (existenceTime R M) Ψ ∧
      let τ := existenceTime R M / 4
      let φ := forwardFromLift Ψ
      let y := footpointFromLift Ψ
      ∃ D : Set (ℝ × (X × Z)), IsOpen D ∧
        Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D ∧
        D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4) ∧
        D = (fun q ↦ (q.1, φ q)) '' (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) ∧
        D ⊆ Ω ∧
        ContDiffOn ℝ ∞ φ (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) ∧
        ContDiffOn ℝ ∞ y D ∧
        MapsTo (fun q ↦ (q.1, φ q)) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) D ∧
        MapsTo (fun q ↦ (q.1, y q)) D (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) ∧
        (∀ p ∈ ball p₀ (R / 8), φ (0, p) = p) ∧
        (∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ, y (t, φ (t, p)) = p) ∧
        (∀ q ∈ D, φ (q.1, y q) = q.2) ∧
        (∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ, (φ (t, p)).2 = p.2) ∧
        (∀ q ∈ D, (y q).2 = q.2.2) ∧
        (∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ,
          HasDerivAt (fun s ↦ φ (s, p)) (V (t, φ (t, p))).2 t) ∧
        ContDiffOn ℝ ∞ φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        ContDiffOn ℝ ∞ y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) := by
  obtain ⟨Ψ, hΨ⟩ := NullFlowDependence.exists_comparison_lift hΩ hbuffer hV hR hM hb
  let ε := existenceTime R M
  let τ := ε / 4
  have hε : 0 < ε := existenceTime_pos hR hM
  have hεR : ε ≤ R / 4 := (existenceTime_le hR hM).1
  have hτR : τ ≤ R / 16 := by dsimp [τ]; linarith
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have ht {t : ℝ} (ht : t ∈ Ioo (-τ) τ) : t ∈ Ioo (-ε) ε := by
    dsimp only [τ] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hp {p : X × Z} (hp : p ∈ ball p₀ (R / 8)) :
      ((0 : ℝ), p) ∈ closedBall (0, p₀) (R / 2) := by
    simpa using ball_subset_closedBall (ball_subset_ball (by linarith : R / 8 ≤ R / 2) hp)
  have hlip : LipschitzOnWith ⟨M, hM⟩ V (closedBall (0, p₀) R) :=
    (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun q hq ↦ (hV.contDiffAt (hΩ.mem_nhds (hbuffer hq))).differentiableAt (by simp))
      (fun q hq ↦ by exact_mod_cast (hb q hq).2)
  obtain ⟨D, hD, hsmall, hbig, himage, hφ, hy, hφD, hyD, hi, hyφ, hφy⟩ :=
    buffered_footpoint_chart hR hM hunit hlip (fun q hq ↦ (hb q hq).1)
      hΨ.smooth hΨ.initial (fun q hq t ht ↦ hΨ.hasDerivAt hq ht)
      (fun q hq t ht ↦ hΨ.range q hq t (Ioo_subset_Icc_self ht))
  have htime (p) (hpin : p ∈ ball p₀ (R / 8)) (t) (htin : t ∈ Ioo (-τ) τ) :
      Ψ ((0, p), t) = (t, forwardFromLift Ψ (t, p)) := by
    refine Prod.ext ?_ rfl
    have hd (s) (hs : s ∈ Ioo (-ε) ε) :
        HasDerivAt (fun s ↦ (Ψ ((0, p), s)).1) 1 s := by
      have hh : HasDerivAt (fun s ↦ (Ψ ((0, p), s)).1) (V (Ψ ((0, p), s))).1 s :=
        (hΨ.hasDerivAt (hp hpin) hs).fst
      simpa only [hunit] using hh
    have he := isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
      (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt)
      differentiableOn_id
      (fun s hs ↦ by rw [(hd s hs).deriv, deriv_id]) h0
      (by simp only [hΨ.initial _ (hp hpin), id_eq]) (ht htin)
    exact he
  have hparam (p) (hpin : p ∈ ball p₀ (R / 8)) (t) (htin : t ∈ Ioo (-τ) τ) :
      (forwardFromLift Ψ (t, p)).2 = p.2 := by
    have hd (s) (hs : s ∈ Ioo (-ε) ε) :
        HasDerivAt (fun s ↦ (Ψ ((0, p), s)).2.2) 0 s := by
      have hh : HasDerivAt (fun s ↦ (Ψ ((0, p), s)).2.2) (V (Ψ ((0, p), s))).2.2 s :=
        (hΨ.hasDerivAt (hp hpin) hs).snd.snd
      simpa only [hparameter] using hh
    have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo _ _).isPreconnected
      (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hd s hs).deriv) (ht htin) h0
    simpa only [forwardFromLift, hΨ.initial _ (hp hpin)] using he
  refine ⟨Ψ, hΨ, D, hD, hsmall, hbig, himage, ?_, hφ, hy.mono hbig,
    hφD, hyD, hi, hyφ, hφy, hparam, ?_, ?_, ?_, ?_⟩
  · intro q hq
    apply hbuffer
    have hq' := hbig hq
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    refine ⟨?_, (mem_ball.mp hq'.2).le.trans (by linarith)⟩
    simpa only [Real.dist_eq, sub_zero] using
      (abs_lt.mpr hq'.1).le.trans (by linarith : τ ≤ R)
  · intro q hq
    have hh := hparam (footpointFromLift Ψ q) (hyD hq).2 q.1 (hyD hq).1
    rw [hφy q hq] at hh
    exact hh.symm
  · intro p hpin t htin
    have hh := (hΨ.hasDerivAt (hp hpin) (ht htin)).snd
    rw [htime p hpin t htin] at hh
    exact hh
  · apply hΨ.smooth.snd.comp
      ((contDiffOn_const.prodMk contDiffOn_snd).prodMk contDiffOn_fst)
    intro q hq
    have hqt : -(2 * (ε / 4)) < q.1 ∧ q.1 < 2 * (ε / 4) := hq.1
    change ((0 : ℝ), q.2) ∈ ball (0, p₀) (R / 2) ∧ q.1 ∈ Ioo (-ε) ε
    constructor
    · simpa using ball_subset_ball (by linarith : R / 4 ≤ R / 2) hq.2
    · constructor <;> linarith [hqt.1, hqt.2]
  · apply hΨ.smooth.snd.comp (contDiffOn_id.prodMk contDiffOn_fst.neg)
    intro q hq
    have hqt : -(2 * (ε / 4)) < q.1 ∧ q.1 < 2 * (ε / 4) := hq.1
    change q ∈ ball (0, p₀) (R / 2) ∧ -q.1 ∈ Ioo (-ε) ε
    constructor
    · rw [mem_ball, Prod.dist_eq, max_lt_iff]
      refine ⟨?_, (mem_ball.mp hq.2).trans (by linarith)⟩
      rw [Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [hqt.1, hqt.2]
    · constructor <;> linarith [hqt.1, hqt.2]

end JanetCartan.ContinuumRow.NormalizedChartFamily
