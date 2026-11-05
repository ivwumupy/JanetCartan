module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence.LiftEstimates

/-!
# Dependence of the same retained forward and inverse maps

Construct comparison lifts on the original low-bound buffers, apply joint
finite-order ODE stability, and identify their restrictions with the supplied
maps by the ODE and inverse identities. No regularity or continuity of a family
of solutions is assumed. The hypotheses are produced by
`ActualAmplitude.UniformFlow` and `ActualAmplitude.LocalConstruction`.

Consumer: the null-flow part of the positive-reference primitive comparison
(`app:ch_background:prop:bg-frame`, `app:ch_osc:prop:osc-normal`, Step 4').
The coefficient-to-immersion comparison and instantiation of the buffers belong
to the parent construction. Scalar-amplitude comparison is a further obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff NNReal Topology

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
open NullTransport.ActualFlow

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem lipschitzOnWith_of_low_bounds
    {Ω : Set (ℝ × E)} {V : ℝ × E → ℝ × E} {p₀ : E} {R M : ℝ}
    (hΩ : IsOpen Ω) (hbuffer : closedBall (0, p₀) R ⊆ Ω)
    (hV : ContDiffOn ℝ ∞ V Ω) (hM : 0 ≤ M)
    (hb : ∀ q ∈ closedBall (0, p₀) R, ‖fderiv ℝ V q‖ ≤ M) :
    LipschitzOnWith ⟨M, hM⟩ V (closedBall (0, p₀) R) :=
  (convex_closedBall (0, p₀) R).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun q hq ↦ (hV.contDiffAt (hΩ.mem_nhds (hbuffer hq))).differentiableAt (by simp))
    (fun q hq ↦ by exact_mod_cast hb q hq)

/-- Construct a comparison lift on precisely the original null-flow buffers,
with the `IsSmoothFlowOn` interface required by the finite-order stability
theorem. The low field bounds produce every field of that interface; in
particular the variational equations are not new premises
(`app:ch_waves:thm:leading`). -/
theorem exists_comparison_lift
    {Ω : Set (ℝ × E)} {V : ℝ × E → ℝ × E} {p₀ : E} {R M : ℝ}
    (hΩ : IsOpen Ω) (hbuffer : closedBall (0, p₀) R ⊆ Ω)
    (hV : ContDiffOn ℝ ∞ V Ω) (hR : 0 < R) (hM : 0 ≤ M)
    (hb : ∀ q ∈ closedBall (0, p₀) R, ‖V q‖ ≤ M ∧ ‖fderiv ℝ V q‖ ≤ M) :
    ∃ Ψ : (ℝ × E) × ℝ → ℝ × E,
      ODE.IsSmoothFlowOn V (0, p₀) R (R / 2) (existenceTime R M) Ψ := by
  exact ODE.exists_smoothFlowOn_of_bounds (L := ⟨M, hM⟩) hΩ hbuffer hV hR.le (half_pos hR).le
    (existenceTime_pos hR hM)
    (lipschitzOnWith_of_low_bounds hΩ hbuffer hV hM (fun q hq ↦ (hb q hq).2))
    (fun q hq ↦ (hb q hq).1)
    (show M * existenceTime R M ≤ R - R / 2 from
      (existenceTime_le hR hM).2.trans (by linarith))

omit [FiniteDimensional ℝ E] in
private theorem retained_eqOn_comparison
    {V : ℝ × E → ℝ × E} {Ψ : (ℝ × E) × ℝ → ℝ × E}
    {Φ Y : ℝ × E → E} {D : Set (ℝ × E)} {p₀ : E} {R T τ : ℝ} {M : ℝ≥0}
    (hR : 0 < R) (hτ : 0 < τ) (hτT : τ < T / 2) (hτR : τ ≤ R / 16)
    (hunit : ∀ q, (V q).1 = 1)
    (hlip : LipschitzOnWith M V (closedBall (0, p₀) R))
    (hΨ : ODE.IsSmoothFlowOn V (0, p₀) R (R / 2) T Ψ)
    (hsmall : Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D)
    (hbig : D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4))
    (hΦD : MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) D)
    (hYD : MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)))
    (hi : ∀ p ∈ ball p₀ (R / 8), Φ (0, p) = p)
    (hd : ∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s ↦ Φ (s, p)) (V (t, Φ (t, p))).2 t)
    (hΦY : ∀ q ∈ D, Φ (q.1, Y q) = q.2) :
    EqOn Φ (forwardFromLift Ψ) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) ∧
      EqOn Y (footpointFromLift Ψ) (Ioo (-τ) τ ×ˢ ball p₀ (R / 32)) := by
  have hr : MapsTo (fun q ↦ (q.1, Φ q))
      (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) (closedBall (0, p₀) R) := by
    intro q hq
    have h := hbig (hΦD hq)
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    exact ⟨by simpa only [Real.dist_eq, sub_zero] using
      (abs_le.mpr ⟨h.1.1.le, h.1.2.le⟩).trans (by linarith : τ ≤ R),
      (mem_ball.mp h.2).le.trans (by linarith)⟩
  exact ⟨forward_eq_of_lift hR hτ (by linarith : τ ≤ T) hunit hlip hΨ hi hd hr,
    (footpoint_eq_of_lift hR hτ hτT hτR hunit hlip hΨ hi hd hr hbig hYD hΦY).mono hsmall⟩

private theorem cNorm_restriction_sub_le
    {Ψ Ψ₀ : (ℝ × E) × ℝ → ℝ × E} {p₀ : E} {R T τ : ℝ}
    {KΦ KY : Set (ℝ × E)} (hR : 0 < R) (hτT : τ < T) (hτR : τ ≤ R / 16)
    (hKΦ : KΦ ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 8))
    (hKY : KY ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 32))
    (hΨ : ContDiffOn ℝ ∞ Ψ (ball (0, p₀) (R / 2) ×ˢ Ioo (-T) T))
    (hΨ₀ : ContDiffOn ℝ ∞ Ψ₀ (ball (0, p₀) (R / 2) ×ˢ Ioo (-T) T))
    (m : ℕ) :
    cNorm KΦ m (forwardFromLift Ψ - forwardFromLift Ψ₀) +
        cNorm KY m (footpointFromLift Ψ - footpointFromLift Ψ₀) ≤
      cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) m
          (forwardFromLift Ψ - forwardFromLift Ψ₀) +
        cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) m
          (footpointFromLift Ψ - footpointFromLift Ψ₀) := by
  let S := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
  let W := ball ((0 : ℝ), p₀) (R / 2) ×ˢ Ioo (-T) T
  have hW : IsOpen W := isOpen_ball.prod isOpen_Ioo
  have hKΦS : KΦ ⊆ S := hKΦ.trans (prod_mono Ioo_subset_Icc_self ball_subset_closedBall)
  have hKYS : KY ⊆ S := hKY.trans (prod_mono Ioo_subset_Icc_self
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))))
  have hsmooth (L : (ℝ × E) →L[ℝ] (ℝ × E) × ℝ) (hL : MapsTo L S W) :
      ∀ q ∈ S, ContDiffAt ℝ m (fun q ↦ ((Ψ - Ψ₀) (L q)).2) q := by
    intro q hq
    exact (((hΨ.sub hΨ₀).contDiffAt (hW.mem_nhds (hL hq))).comp q
      L.contDiff.contDiffAt).snd.of_le (by simp)
  apply add_le_add
  · apply cNorm_mono_set_of_contDiffAt hKΦS (isCompact_Icc.prod (isCompact_closedBall _ _))
    apply hsmooth forwardLiftInput
    rintro ⟨t, p⟩ ⟨ht, hp⟩
    refine ⟨?_, ?_⟩
    · change ((0 : ℝ), p) ∈ ball (0, p₀) (R / 2)
      simpa using (closedBall_subset_ball (by linarith : R / 8 < R / 2) hp)
    · change -T < t ∧ t < T
      constructor <;> linarith [ht.1, ht.2]
  · apply cNorm_mono_set_of_contDiffAt hKYS (isCompact_Icc.prod (isCompact_closedBall _ _))
    apply hsmooth backwardLiftInput
    rintro ⟨t, p⟩ ⟨ht, hp⟩
    refine ⟨?_, ?_⟩
    · change (t, p) ∈ ball (0, p₀) (R / 2)
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨by simpa only [Real.dist_eq, sub_zero] using
        (abs_le.mpr ht).trans_lt (by linarith : τ < R / 2),
        hp.trans_lt (by linarith)⟩
    · change -T < -t ∧ -t < T
      constructor <;> linarith [ht.1, ht.2]

/-- At a fixed reference, every finite joint seminorm of the SAME retained
forward map and inverse ODE map is continuous in the lifted coefficient.
The threshold precedes the varying coefficient, maps and flow tube. The only
solution premises are the original initial value, ODE, range and inverse
identities from `ActualAmplitude.UniformFlow`; comparison lifts and their
identification are proved here (`app:ch_background:prop:bg-frame`).

The physical direction supplies this lifted-field difference through
`exists_liftedDirection_sub_bound`. The parent owns the immersion-level input.
The forward working set lies inside the original initial-label cylinder; the
inverse working set lies inside the covered box. This allows evaluation of the
forward map at the actual inverse labels in the characteristic integral. -/
theorem exists_cNorm_retained_characteristics_sub_lt
    {Ω : Set (ℝ × E)} {p₀ : E} {R M τ : ℝ}
    {KΦ KY : Set (ℝ × E)} {V₀ : ℝ × E → ℝ × E}
    {D₀ : Set (ℝ × E)} {Φ₀ Y₀ : ℝ × E → E}
    (hΩ : IsOpen Ω) (hbuffer : closedBall (0, p₀) R ⊆ Ω)
    (hR : 0 < R) (hM : 0 ≤ M) (hτ : 0 < τ)
    (hτT : τ < existenceTime R M / 2) (hτR : τ ≤ R / 16)
    (hKΦ : KΦ ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 8))
    (hKY : KY ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 32))
    (hV₀ : ContDiffOn ℝ ∞ V₀ Ω) (hunit₀ : ∀ q, (V₀ q).1 = 1)
    (hb₀ : ∀ q ∈ closedBall (0, p₀) R, ‖V₀ q‖ ≤ M ∧ ‖fderiv ℝ V₀ q‖ ≤ M)
    (hsmall₀ : Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D₀)
    (hbig₀ : D₀ ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4))
    (hΦD₀ : MapsTo (fun q ↦ (q.1, Φ₀ q)) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) D₀)
    (hYD₀ : MapsTo (fun q ↦ (q.1, Y₀ q)) D₀ (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)))
    (hi₀ : ∀ p ∈ ball p₀ (R / 8), Φ₀ (0, p) = p)
    (hd₀ : ∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s ↦ Φ₀ (s, p)) (V₀ (t, Φ₀ (t, p))).2 t)
    (hΦY₀ : ∀ q ∈ D₀, Φ₀ (q.1, Y₀ q) = q.2)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (V : ℝ × E → ℝ × E) (Φ Y : ℝ × E → E) (D : Set (ℝ × E)),
      ContDiffOn ℝ ∞ V Ω → (∀ q, (V q).1 = 1) →
      (∀ q ∈ closedBall (0, p₀) R, ‖V q‖ ≤ M ∧ ‖fderiv ℝ V q‖ ≤ M) →
      Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D →
      D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4) →
      MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) D →
      MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) →
      (∀ p ∈ ball p₀ (R / 8), Φ (0, p) = p) →
      (∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ,
        HasDerivAt (fun s ↦ Φ (s, p)) (V (t, Φ (t, p))).2 t) →
      (∀ q ∈ D, Φ (q.1, Y q) = q.2) →
      cNorm (closedBall (0, p₀) R) m (V - V₀) < δ →
      cNorm KΦ m (Φ - Φ₀) + cNorm KY m (Y - Y₀) < ε := by
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_comparison_lift hΩ hbuffer hV₀ hR hM hb₀
  have hlip₀ := lipschitzOnWith_of_low_bounds hΩ hbuffer hV₀ hM (fun q hq ↦ (hb₀ q hq).2)
  have he₀ := retained_eqOn_comparison hR hτ hτT hτR hunit₀ hlip₀ hΨ₀
    hsmall₀ hbig₀ hΦD₀ hYD₀ hi₀ hd₀ hΦY₀
  have htime : τ < existenceTime R M := by linarith
  obtain ⟨δ, hδ, hb⟩ := exists_cNorm_lift_characteristics_sub_lt hΩ hbuffer hR
    hV₀ hΨ₀ hτ htime (by linarith : τ ≤ R / 4) m hε
  refine ⟨δ, hδ, ?_⟩
  intro V Φ Y D hV hunit hlow hsmall hbig hΦD hYD hi hd hΦY hclose
  obtain ⟨Ψ, hΨ⟩ := exists_comparison_lift hΩ hbuffer hV hR hM hlow
  have hlip := lipschitzOnWith_of_low_bounds hΩ hbuffer hV hM (fun q hq ↦ (hlow q hq).2)
  have he := retained_eqOn_comparison hR hτ hτT hτR hunit hlip hΨ
    hsmall hbig hΦD hYD hi hd hΦY
  have hnorm {K W : Set (ℝ × E)} (hW : IsOpen W) (hKW : K ⊆ W)
      {f g f' g' : ℝ × E → E} (hf : EqOn f f' W) (hg : EqOn g g' W) :
      cNorm K m (f - g) = cNorm K m (f' - g') := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
    intro q hq
    filter_upwards [hW.mem_nhds (hKW hq)] with p hp
    exact congrArg₂ (· - ·) (hf hp) (hg hp)
  rw [hnorm (isOpen_Ioo.prod isOpen_ball) hKΦ he.1 he₀.1,
    hnorm (isOpen_Ioo.prod isOpen_ball) hKY he.2 he₀.2]
  exact (cNorm_restriction_sub_le hR htime hτR hKΦ hKY hΨ.smooth hΨ₀.smooth m).trans_lt
    (hb V Ψ hV hΨ hclose)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
