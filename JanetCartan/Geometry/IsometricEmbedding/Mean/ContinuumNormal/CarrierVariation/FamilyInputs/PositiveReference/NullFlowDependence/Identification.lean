module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.FlowStability.Joint
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.JetBounds

/-!
# Identification of retained null characteristics

The comparison flow may be constructed independently of the maps retained by
`exists_projected_local_positive_amplitude`. ODE uniqueness identifies its
zero-section restriction with that SAME forward map. Reversal and the retained
inverse identities then identify its backwards restriction with the SAME `Y`.
The inputs below are equations and range buffers, not continuity assumptions.

Consumer: coefficient dependence of the positive-reference scalar in
`app:ch_background:prop:bg-frame`; source: `app:ch_waves:thm:leading`.
`ActualAmplitude.UniformFlow` produces the initial, ODE, range and inverse
premises, with `τ = existenceTime R M / 4`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff NNReal

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
open NullTransport.ActualFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original forward null map is the restriction of any comparison lift
solving its ODE on the common buffers (`app:ch_waves:thm:leading`). This
identification is needed before applying finite-order flow stability. -/
theorem forward_eq_of_lift
    {V : ℝ × E → ℝ × E} {Ψ : (ℝ × E) × ℝ → ℝ × E}
    {Φ : ℝ × E → E} {p₀ : E} {R T τ : ℝ} {M : ℝ≥0}
    (hR : 0 < R) (hτ : 0 < τ) (hτT : τ ≤ T)
    (hunit : ∀ q, (V q).1 = 1)
    (hlip : LipschitzOnWith M V (closedBall (0, p₀) R))
    (hΨ : ODE.IsSmoothFlowOn V (0, p₀) R (R / 2) T Ψ)
    (hi : ∀ p ∈ ball p₀ (R / 8), Φ (0, p) = p)
    (hd : ∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s ↦ Φ (s, p)) (V (t, Φ (t, p))).2 t)
    (hr : MapsTo (fun q ↦ (q.1, Φ q))
      (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) (closedBall (0, p₀) R)) :
    EqOn Φ (forwardFromLift Ψ) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) := by
  rintro ⟨t, p⟩ ⟨ht, hp⟩
  have hp' : ((0 : ℝ), p) ∈ closedBall (0, p₀) (R / 2) := by
    simpa using (ball_subset_closedBall
      (ball_subset_ball (by linarith : R / 8 ≤ R / 2) hp))
  have ht' {s : ℝ} (hs : s ∈ Ioo (-τ) τ) : s ∈ Ioo (-T) T := by
    constructor <;> linarith [hs.1, hs.2]
  have heq := ODE_solution_unique_of_mem_Ioo (v := fun _ ↦ V)
    (s := fun _ ↦ closedBall (0, p₀) R)
    (f := fun s ↦ (s, Φ (s, p))) (g := fun s ↦ Ψ ((0, p), s))
    (fun _ _ ↦ hlip)
    (show (0 : ℝ) ∈ Ioo (-τ) τ from ⟨neg_neg_of_pos hτ, hτ⟩)
    (fun s hs ↦ ⟨by
      have hv : V (s, Φ (s, p)) = (1, (V (s, Φ (s, p))).2) :=
        Prod.ext (hunit _) rfl
      rw [hv]
      exact (hasDerivAt_id s).prodMk (hd p hp s hs),
      hr (x := (s, p)) ⟨hs, hp⟩⟩)
    (fun s hs ↦ ⟨hΨ.hasDerivAt hp' (ht' hs),
      hΨ.range _ hp' _ (Ioo_subset_Icc_self (ht' hs))⟩)
    (by rw [hi p hp, hΨ.initial _ hp'])
  exact congrArg Prod.snd (heq ht)

/-- The original inverse ODE label is the backwards restriction of any
comparison lift. The range and right-inverse premises are exactly those
retained by `ActualAmplitude.UniformFlow`; uniqueness proves the identification
rather than assuming it (`app:ch_waves:thm:leading`). -/
theorem footpoint_eq_of_lift
    {V : ℝ × E → ℝ × E} {Ψ : (ℝ × E) × ℝ → ℝ × E}
    {Φ Y : ℝ × E → E} {D : Set (ℝ × E)} {p₀ : E} {R T τ : ℝ} {M : ℝ≥0}
    (hR : 0 < R) (hτ : 0 < τ) (hτT : τ < T / 2) (hτR : τ ≤ R / 16)
    (hunit : ∀ q, (V q).1 = 1)
    (hlip : LipschitzOnWith M V (closedBall (0, p₀) R))
    (hΨ : ODE.IsSmoothFlowOn V (0, p₀) R (R / 2) T Ψ)
    (hi : ∀ p ∈ ball p₀ (R / 8), Φ (0, p) = p)
    (hd : ∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s ↦ Φ (s, p)) (V (t, Φ (t, p))).2 t)
    (hr : MapsTo (fun q ↦ (q.1, Φ q))
      (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) (closedBall (0, p₀) R))
    (hD : D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4))
    (hY : MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)))
    (hΦY : ∀ q ∈ D, Φ (q.1, Y q) = q.2) :
    EqOn Y (footpointFromLift Ψ) D := by
  have hT : 0 < T := by linarith
  have hf := forward_eq_of_lift hR hτ (by linarith : τ ≤ T)
    hunit hlip hΨ hi hd hr
  intro q hq
  have hlabel := hY hq
  have hp : ((0 : ℝ), Y q) ∈ closedBall (0, p₀) (R / 2) := by
    simpa using (ball_subset_closedBall
      (ball_subset_ball (by linarith : R / 8 ≤ R / 2) hlabel.2))
  have ht : q.1 ∈ Ioo (-T / 2) (T / 2) := by
    constructor <;> linarith [hlabel.1.1, hlabel.1.2]
  have htime : (Ψ ((0, Y q), q.1)).1 = q.1 := by
    have hdt (s) (hs : s ∈ Ioo (-T) T) :
        HasDerivAt (fun s ↦ (Ψ ((0, Y q), s)).1) 1 s := by
      have h : HasDerivAt (fun s ↦ (Ψ ((0, Y q), s)).1)
          (V (Ψ ((0, Y q), s))).1 s := (hΨ.hasDerivAt hp hs).fst
      rwa [hunit] at h
    have he := isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
      (fun s hs ↦ (hdt s hs).differentiableAt.differentiableWithinAt)
      differentiable_id.differentiableOn
      (fun s hs ↦ by rw [(hdt s hs).deriv, deriv_id])
      (show (0 : ℝ) ∈ Ioo (-T) T from ⟨neg_neg_of_pos hT, hT⟩)
      (by simp only [hΨ.initial _ hp, id_eq])
    exact he (by constructor <;> linarith [ht.1, ht.2])
  have hforward : Ψ ((0, Y q), q.1) = q := by
    apply Prod.ext htime
    exact (hf hlabel).symm.trans (hΦY q hq)
  have hqball : q ∈ closedBall (0, p₀) (R / 2) := by
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    refine ⟨?_, (mem_ball.mp (hD hq).2).le.trans (by linarith)⟩
    simpa only [Real.dist_eq, sub_zero] using
      (abs_le.mpr ⟨hlabel.1.1.le, hlabel.1.2.le⟩).trans (by linarith : τ ≤ R / 2)
  have he := reverse_flow_eq hT hlip hΨ.initial
    (fun _ hx _ ht ↦ hΨ.hasDerivAt hx ht)
    (fun x hx t ht ↦ hΨ.range x hx t (Ioo_subset_Icc_self ht)) hp ht
    (hforward.symm ▸ hqball)
  rw [hforward] at he
  exact (congrArg Prod.snd he).symm

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
